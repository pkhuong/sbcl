/* Support for either scavenged or mark/sweep and scavenged regions
 * in the foreign heap.
 *
 * Scavenged-only regions are easy: they are treated as additional
 * roots and otherwise managed manually.
 *
 * Otherwise, a weak generational mark/sweep model is used:
 * GCed regions are either dead, adult or teenaged.
 *
 * Dead regions are only waiting to be deallocated; their contents
 * are completely ignored and may contain wild pointers. Outside GCs,
 * these regions are in the dead_allocations list.
 *
 * Adult regions may be pointed to by random places in the heap;
 * they can only be GCed on full collections. These regions are in
 * the live_allocations list.
 *
 * Teenaged regions are only pointed to by roots; they are GCed
 * at every collection (until they pass majority). These regions are
 * in the maybe_live_allocations list.
 *
 * A region is only in limbo during GC. Once the GC is done, any
 * region still in limbo is dead. During GC, they are only found in
 * maybe_live_allocations.
 *
 * The first step of any GC is to scavenge (scan in our case) the roots.
 * Teenaged regions are demoted in limbo. When scanning roots, regions
 * in limbo become teenagers. When we're done scanning roots, these reborn
 * regions are scavenged, but remain on the white list: they could still
 * pass majority.
 *
 * When scanning the general heap, teenaged or in-limbo regions become
 * adults. Since teenaged regions have already been scavenged, only
 * those in limbo are put on a to-scavenge list (newly_live_regions).
 *
 * While scavenging the new_space, we also scavenge newly_live_regions,
 * before splicing it into live_regions.
 *
 * When we're done GCing, any region in maybe_live that's still in limbo
 * is dead, while teenaged regions remain there.
 *
 * On full GCs, everything is a rejuvenated as in limbo.
 *
 * In the actual implementation, pointers into foreign allocations aren't
 * followed immediately.  Instead, they are accumulated in a buffer, and
 * that buffer is processed from time to time.
 */

#include <stdlib.h>
#include <stdint.h>
#include "sbcl.h"
#include "runtime.h"
#include "gc-internal.h"
#include "genesis/sap.h"
#include "gencgc-internal.h"
#include "foreign-allocation.h"

#ifdef LISP_FEATURE_SB_THREAD
pthread_mutex_t foreign_allocation_lock = PTHREAD_MUTEX_INITIALIZER;
#endif

struct foreign_allocation * always_live_allocations = 0;
// to sweep
struct foreign_allocation * dead_allocations = 0;
// white: if partial GC, filled with limbo and teens
//         if full GC, filled with everything.
struct foreign_allocation * maybe_live_allocations = 0;

// same list available as a vector for bsearch.
typedef struct {
    lispobj * key;
    union { struct foreign_allocation * alloc; unsigned long next; } val;
} search_item_t;

size_t limbo_vec_count = 0;
size_t limbo_vec_size  = 0;
search_item_t * limbo_vec = 0;
size_t limbo_vec_deleted = 0;

// grey
struct foreign_allocation * newly_live_allocations = 0;
// black
struct foreign_allocation * live_allocations = 0;

// mask of all the type of objects found in maybe_live
int all_type_masks = 0;
unsigned scanning_roots_p = 0;

void enqueue_allocation (struct foreign_allocation ** queue,
                         struct foreign_allocation * allocation)
{
    gc_assert(!allocation->prev);
    gc_assert(!allocation->next);

    if (!*queue) {
        allocation->prev = allocation->next = allocation;
        *queue = allocation;
        return;
    }

    allocation->next = (*queue)->next;
    allocation->next->prev = allocation;

    (*queue)->next = allocation;
    allocation->prev = *queue;
}


void dequeue_allocation (struct foreign_allocation ** queue,
                         struct foreign_allocation * allocation)
{
    if (allocation->prev == allocation) {
        gc_assert(allocation->next == allocation);
        *queue = 0;
    } else {
        allocation->next->prev = allocation->prev;
        allocation->prev->next = allocation->next;
    }

    allocation->next = allocation->prev = 0;
}



void splice_allocations (struct foreign_allocation ** dest,
                         struct foreign_allocation * queue)
{
    if (!queue) return;

    if (!*dest) {
        *dest = queue;
        return;
    }

    struct foreign_allocation
        * first_queue = queue,
        * last_queue  = queue->prev,
        * first_dest  = *dest,
        * last_dest   = (*dest)->prev;

    last_dest->next    = first_queue;
    first_queue->prev  = last_dest;

    last_queue->next   = first_dest;
    first_dest->prev   = last_queue;
}

struct foreign_allocation * pop_allocation (struct foreign_allocation ** queue)
{
    if (!*queue)
        return 0;

    struct foreign_allocation * ret = *queue;
    dequeue_allocation (queue, ret);
    return ret;
}

void register_always_live_allocation (struct foreign_allocation * allocation)
{
    allocation->state = -1;

    enqueue_allocation(&always_live_allocations, allocation);
}

void retire_always_live_allocation (struct foreign_allocation * allocation)
{
    gc_assert(-1 == allocation->state);

    dequeue_allocation(&always_live_allocations, allocation);
}

void register_gced_allocation (struct foreign_allocation * allocation)
{
    allocation->state = 1;
    enqueue_allocation(&maybe_live_allocations, allocation);
}

void retire_gced_allocation (struct foreign_allocation * allocation)
{
    struct foreign_allocation ** queue;

    switch (allocation->state) {
    case 0: queue = &dead_allocations;
        break;
    case 1: queue = &maybe_live_allocations;
        break;
    case 2: queue = &live_allocations;
        break;
    default:
        lose("Bad allocation state (%i) for GCed allocation %p",
             allocation->state, allocation);
        return;
    }

    dequeue_allocation(queue, allocation);
}

typedef struct {
    lispobj * ptr;
}foreign_ref_t;

unsigned long foreign_pointer_count = 0;
unsigned long foreign_pointer_size = 0;
foreign_ref_t * foreign_pointer_vector = 0;

void (*enqueue_lisp_pointer)(lispobj *) = 0;

void enqueue_random_pointer (lispobj * ptr)
{
    if (!maybe_live_allocations) return;
    if (ptr < maybe_live_allocations->start) return;
    if (ptr >= maybe_live_allocations->prev->end) return;

    if (foreign_pointer_count >= foreign_pointer_size)
        process_foreign_pointers();

    foreign_pointer_vector[foreign_pointer_count].ptr = ptr;
    foreign_pointer_count++;
}

void enqueue_sap_pointer (void * ptr)
{
    gc_assert(!scanning_roots_p);
    if (!maybe_live_allocations) return;
    if ((lispobj*) ptr < maybe_live_allocations->start) return;
    if ((lispobj*) ptr >= maybe_live_allocations->prev->end) return;

    if (foreign_pointer_count >= foreign_pointer_size)
        process_foreign_pointers();

    foreign_pointer_vector[foreign_pointer_count].ptr
        = (lispobj*) (((lispobj)ptr) & (~1UL));
    foreign_pointer_count++;
}

lispobj (*default_trans_sap)(lispobj obj) = 0;

static lispobj
trans_sap(lispobj object)
{
    gc_assert(is_lisp_pointer(object));
    enqueue_sap_pointer(((struct sap *)native_pointer(object))->pointer);

    return copy_unboxed_object(object, 2);
}

static int cmp_foreign_pointers (const void * a, const void * b)
{
    const foreign_ref_t * x = a;
    const foreign_ref_t * y = b;

    if (x->ptr < y->ptr)
        return -1;
    if (x->ptr == y->ptr)
        return 0;
    return 1;
}

static void sort_foreign_pointers ()
{
    qsort(foreign_pointer_vector,
          foreign_pointer_count, sizeof(foreign_ref_t),
          cmp_foreign_pointers);
}

static inline
void maybe_repack_limbo_vec ()
{
    unsigned long alloc, i;
    if (limbo_vec_deleted < limbo_vec_count/2) return;

    for (alloc = 0, i = 0; i < limbo_vec_count; i++)
        if (!(limbo_vec[i].val.next&1))
            limbo_vec[alloc++] = limbo_vec[i];

    limbo_vec_deleted = 0;
    limbo_vec_count = alloc;
}

static inline
int find_live_region (unsigned long * index_ptr, long delta)
{
#define RET(OUT, VALUE) do { *index_ptr = (OUT); return (VALUE); } while (0)
    unsigned long index = *index_ptr + delta, prev = index;

    if (index >= limbo_vec_count) RET(limbo_vec_count-1, 1);
    if (!(limbo_vec[index].val.next&1)) RET(index, 0); // it's alive!

    while (index < limbo_vec_count) {
        unsigned long next = limbo_vec[prev ].val.next
                           = limbo_vec[index].val.next;
        if (!(next&1)) RET(index, 0);
        prev = index;
        index = next >> 1;
    }

    RET(limbo_vec_count-1, 1);
#undef RET
}

// find first alloc s.t. alloc->end > ptr
static
int find_region_for_pointer (lispobj * ptr, unsigned long * index_ptr)
{
#define NEXT(DELTA) do {                                                \
        if (find_live_region(index_ptr, (DELTA))) return 1;             \
        if (limbo_vec[*index_ptr].val.alloc->end > ptr) return 0;       \
    } while (0)
    unsigned long incr, low, high;

    NEXT(0);
    NEXT(1);

    incr = 2;
    low = high = *index_ptr;
    // find range s.t. low.start <= ptr < high.start
    while (limbo_vec[high].key < ptr) {
        low   = high;
        high += incr;
        incr *= 2;

        if (!(high < limbo_vec_count)) {
            *index_ptr = limbo_vec_count-1;
            if (find_live_region(index_ptr, 0)) return 1;
            high = *index_ptr;
            if (limbo_vec[high].val.alloc->end <= ptr) return 1;
            break;
        }
    }
    // tighten range: low is last alloc s.t. low.start <= ptr.
    //  --> first alloc s.t. end > ptr is low or next one.
    while ((high-low) > 1) {
        unsigned long mid = low + (high-low)/2;
        lispobj   * pivot = limbo_vec[mid].key;
        if (pivot <= ptr) low  = mid;
        else              high = mid;
    }

    *index_ptr = low;

    NEXT(0);
    return find_live_region(index_ptr, 1);
#undef NEXT
}

// first pointer s.t. ptr >= alloc.start
static
int find_pointer_for_region(struct foreign_allocation * alloc,
                            unsigned long * index_ptr,
                            long delta)
{
#define RET(OUT, VALUE) do { *index_ptr = (OUT); return (VALUE); } while (0)
    unsigned long low = *index_ptr + delta, high;
    lispobj * start = alloc->start;

    if (low >= foreign_pointer_count) RET(foreign_pointer_count-1, 1);
    if (foreign_pointer_vector[low].ptr >= start) return 0;
    if (++low >= foreign_pointer_count) RET(foreign_pointer_count-1, 1);
    if (foreign_pointer_vector[low].ptr >= start) RET(low, 0);

    {
        unsigned long incr = 2;
        high = low;

        // range s.t. low.ptr < start <= high.ptr
        while (foreign_pointer_vector[high].ptr < start) {
            low = high;
            high += incr;
            incr *= 2;

            if (high >= foreign_pointer_count) {
                high = foreign_pointer_count-1;
                if (foreign_pointer_vector[high].ptr < start) RET(high, 1);
                break;
            }
        }
    }

    // tighten s.t. low.ptr < start <= high.ptr
    while ((high-low) > 1) {
        unsigned long mid = low + (high-low)/2;
        lispobj * ptr     = foreign_pointer_vector[mid].ptr;

        if (ptr < start) low = mid;
        else             high = mid;
    }

    RET(high, 0);
#undef RET
}

static inline
int process_pointer_alloc_pair_p (foreign_ref_t foreign, struct foreign_allocation * alloc)
{
#if defined(LISP_FEATURE_X86) || defined(LISP_FEATURE_X86_64)
    lispobj * enclosing;
#endif
    if (alloc->type & 1) { // any pointer counts!
        // SAP's low bit is cleared, so either it's a preserved pointer
        // (and we're scanning roots), or it's not a lisp pointer.
        if (scanning_roots_p || !is_lisp_pointer((lispobj)foreign.ptr))
            return 1;
    }

    if (alloc->type & 4) { // pointer to head counts
        if (scanning_roots_p) { // we're scanning roots, it's preserved
            if (alloc->start == foreign.ptr) return 1;
        } else if (!is_lisp_pointer((lispobj)foreign.ptr)) {
            // otherwise low bit cleared on SAP addresses
            if (((lispobj)alloc->start & (~1UL)) == (lispobj)foreign.ptr)
                return 1;
        }
    }

    if (!(alloc->type & 2)) return 0;

    /* Lisp-like heap: */
    if (!(is_lisp_pointer((lispobj)foreign.ptr)||scanning_roots_p)) return 0;

#if defined(LISP_FEATURE_X86) || defined(LISP_FEATURE_X86_64)
    if (!(enclosing
          = gc_search_space(alloc->start, alloc->end - alloc->start, foreign.ptr)))
        return 0;

    if (!looks_like_valid_lisp_pointer_p(foreign.ptr, enclosing)) return 0;
#endif

    return 1;
}

void process_foreign_pointers ()
{
    unsigned long foreign_index;
    unsigned long alloc_index;

    if (!(maybe_live_allocations && foreign_pointer_count)) goto done;

    sort_foreign_pointers();
    maybe_repack_limbo_vec();
    foreign_index = 0;
    alloc_index = 0;

    if (!find_live_region(&alloc_index, 0)) goto done;

    while (1) {
        foreign_ref_t foreign = foreign_pointer_vector[foreign_index];
        struct foreign_allocation * alloc = limbo_vec[alloc_index].val.alloc;

        while (!(alloc->start <= foreign.ptr && foreign.ptr < alloc->end)) {
            if (!(foreign.ptr < alloc->end)) {
                if (find_region_for_pointer(foreign.ptr, &alloc_index))
                    goto done;
                alloc = limbo_vec[alloc_index].val.alloc;
                if (scanning_roots_p && (1 == alloc->state))
                    do {
                        if (find_live_region(&alloc_index, 1)) goto done;
                        alloc = limbo_vec[alloc_index].val.alloc;
                    } while (1 == alloc->state);
            }

            if (!(alloc->start <= foreign.ptr)) {
                if (find_pointer_for_region(alloc, &foreign_index, 0)) goto done;
                foreign = foreign_pointer_vector[foreign_index];
            }
        }

        if (process_pointer_alloc_pair_p(foreign, alloc)) {
            if (scanning_roots_p) {
                alloc->state = 1;
            } else {
                dequeue_allocation(&maybe_live_allocations, alloc);
                enqueue_allocation((1 == alloc->state) ? &live_allocations
                                                       : &newly_live_allocations,
                                   alloc);
                alloc->state = 2;
                limbo_vec_deleted++;
                limbo_vec[alloc_index].val.next = ((alloc_index+1)<<1)|1;
            }

            if (find_live_region(&alloc_index, 1)) goto done;
        }

        if (find_pointer_for_region(alloc, &foreign_index, 1)) goto done;
    }

    done:
    foreign_pointer_count = 0;
}

static int cmp_search_item (const void * a, const void * b)
{
    const search_item_t * x = a;
    const search_item_t * y = b;

    if (x->key < y->key)
        return -1;

    if (x->key == y->key)
        return 0;

    return 1;
}

// only the vector needs to be sorted!
static void sort_gced_allocations ()
{
    struct foreign_allocation * ptr;
    all_type_masks = 0;
    if (!maybe_live_allocations)
        return;
    /* Blit the list to a vector */
    limbo_vec_count   = 0;
    limbo_vec_deleted = 0;
    if (!limbo_vec_size) {
        limbo_vec = realloc(limbo_vec, 1024*sizeof(search_item_t));
        gc_assert(limbo_vec);
        limbo_vec_size = 1024;
    }

    ptr = maybe_live_allocations;
    do {
        if (limbo_vec_count >= limbo_vec_size) {
            limbo_vec
                = realloc(limbo_vec,
                          sizeof(search_item_t)
                          * limbo_vec_size * 2);
            gc_assert(limbo_vec);
            limbo_vec_size *= 2;
        }

        ptr->state = 0;
        limbo_vec[limbo_vec_count].key = ptr->start;
        limbo_vec[limbo_vec_count].val.alloc = ptr;
        all_type_masks |= ptr->type;
        limbo_vec_count++;
    } while ((ptr = ptr->next) != maybe_live_allocations);

    gc_assert(limbo_vec_count);

    /* sort the vector */
    qsort(limbo_vec, limbo_vec_count, sizeof(search_item_t), cmp_search_item);

    if (limbo_vec_count) {
        unsigned long nlpo2 = limbo_vec_count;
        nlpo2 |= nlpo2 >> 1;
        nlpo2 |= nlpo2 >> 2;
        nlpo2 |= nlpo2 >> 4;
        nlpo2 |= nlpo2 >> 8;
        nlpo2 |= nlpo2 >> 16;
        if (sizeof(unsigned long) > 4)
            nlpo2 |= nlpo2 >> 32;

        limbo_vec_size = nlpo2+1;
        limbo_vec = realloc(limbo_vec, sizeof(search_item_t) * nlpo2);
        gc_assert(limbo_vec);
    } else {
        limbo_vec_size = 0;
        free(limbo_vec);
        limbo_vec = 0;
    }
}

void prepare_foreign_allocations_for_gc (int full_gc_p)
{
    default_trans_sap = transother[SAP_WIDETAG];
    newly_live_allocations = 0;
    foreign_pointer_count = 0;
    foreign_pointer_size = 1024*1024;
    foreign_pointer_vector = realloc(foreign_pointer_vector,
                                     1024*1024*sizeof(lispobj *));
    scanning_roots_p = 1;
    if (full_gc_p) {
        splice_allocations(&maybe_live_allocations, live_allocations);
        live_allocations = 0;
    }

    sort_gced_allocations();
    if (all_type_masks&(1|4))
        transother[SAP_WIDETAG] = trans_sap;

    enqueue_lisp_pointer
        = (all_type_masks&2)
        ? enqueue_random_pointer
        : 0;
}

void scavenge_foreign_allocations (struct foreign_allocation * allocations)
{
    struct foreign_allocation * ptr;
    if (!allocations) return;

    ptr = allocations;
    do {
        if (!(ptr->type & 8)) continue;
        scavenge(ptr->start, ptr->end - ptr->start);
        gc_assert(!from_space_p(*ptr->start));
        ptr = ptr->next;
    } while ((ptr = ptr->next) != allocations);
}

/* execute once all the roots have been scavenged */
void scavenge_teenaged_alloc ()
{
    struct foreign_allocation * ptr;
    process_foreign_pointers();

    if (!scanning_roots_p) return;

    scanning_roots_p = 0;

    if (!maybe_live_allocations) return;

    ptr = maybe_live_allocations;
    do {
        if ((1 == ptr->state) && (ptr->type & 8))
            scavenge(ptr->start, ptr->end-ptr->start);
    } while ((ptr = ptr->next) != maybe_live_allocations);
}

void mark_foreign_alloc ()
{
    gc_assert(!scanning_roots_p);
    while (foreign_pointer_count || newly_live_allocations) {
        process_foreign_pointers();
        if (newly_live_allocations) {
            scavenge_foreign_allocations(newly_live_allocations);
            splice_allocations(&live_allocations, newly_live_allocations);
            newly_live_allocations = 0;
        }
    }
}

void sweep_allocations ()
{
    struct foreign_allocation * ptr = maybe_live_allocations;

    transother[SAP_WIDETAG] = default_trans_sap;
    enqueue_lisp_pointer = 0;
    gc_assert(0 == newly_live_allocations);
    gc_assert(0 == foreign_pointer_count);

    if (!maybe_live_allocations) return;

    do {
        if (0 == ptr->state) {
            struct foreign_allocation * next = ptr->next;
            dequeue_allocation(&maybe_live_allocations, ptr);
            enqueue_allocation(&dead_allocations, ptr);
            if (!maybe_live_allocations) break;
            ptr = next;
        } else {
            gc_assert(1 == ptr->state);
            ptr = ptr->next;
        }
    } while (ptr != maybe_live_allocations);
}
