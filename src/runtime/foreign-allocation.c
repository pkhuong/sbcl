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
#include "sbcl.h"
#include "runtime.h"
#include "gc-internal.h"
#include "genesis/sap.h"
/* defined in gencgc.c */
int looks_like_valid_lisp_pointer_p(lispobj *pointer, lispobj *start_addr);
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

struct foreign_ref {
    lispobj * ptr;
};
unsigned long foreign_pointer_count = 0;
unsigned long foreign_pointer_size = 0;
struct foreign_ref * foreign_pointer_vector = 0;

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

void (*enqueue_lisp_pointer)(lispobj *) = 0;

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
    const struct foreign_ref * x = a;
    const struct foreign_ref * y = b;

    if (x->ptr < y->ptr)
        return -1;
    if (x->ptr == y->ptr)
        return 0;
    return 1;
}

static void sort_foreign_pointers ()
{
    qsort(foreign_pointer_vector,
          foreign_pointer_count, sizeof(struct foreign_ref),
          cmp_foreign_pointers);
}

void process_foreign_pointers ()
{
    struct foreign_allocation * alloc;
    unsigned i;
    lispobj * search_ptr;
    struct foreign_ref foreign;

    if (!maybe_live_allocations)
        goto done;
    if (!foreign_pointer_count)
        goto done;

    sort_foreign_pointers();

    alloc = maybe_live_allocations;
    search_ptr = alloc->start;
    i = 0;
    foreign = foreign_pointer_vector[0];
#define NEXT_ALLOC                                              \
    do {                                                        \
        alloc = alloc->next;                                    \
        search_ptr = alloc->start;                              \
        if (alloc == maybe_live_allocations) goto done;         \
    } while (0)

#define NEXT_FOREIGN                                    \
    do {                                                \
        if (++i >= foreign_pointer_count) goto done;    \
        foreign = foreign_pointer_vector[i];            \
    } while (0)

    while (maybe_live_allocations) {
        int live_p = 0;
        while (!((alloc->start <= foreign.ptr)
                 && (foreign.ptr < alloc->end))) {
            while (!(foreign.ptr < alloc->end))
                NEXT_ALLOC;

            while (!(foreign.ptr >= alloc->start))
                NEXT_FOREIGN;
        }

        if (alloc->type & 1) { // any pointer counts!
            // SAP's low bit is cleared, so either it's a preserved pointer
            // (and we're scanning roots), or it's not a lisp pointer.
            if (scanning_roots_p || !is_lisp_pointer((lispobj)foreign.ptr)) {
                live_p = 1;
                goto next;
            }
        }

        if (alloc->type & 4) { // pointer to head counts
            if (scanning_roots_p) { // we're scanning roots, it's preserved
                if (alloc->start == foreign.ptr) {
                    live_p = 1;
                    goto next;
                }
            } else if (!is_lisp_pointer((lispobj)foreign.ptr)) {
                // otherwise low bit cleared on SAP addresses
                lispobj start = (lispobj)alloc->start & (~1UL);
                if (start == (lispobj)foreign.ptr) {
                    live_p = 1;
                    goto next;
                }
            }
        }

        if (!(alloc->type & 2)) goto next;

        /* Lisp-like heap: */
        if (!(is_lisp_pointer((lispobj)foreign.ptr)||scanning_roots_p))
            goto next;
        lispobj * enclosing
            = gc_search_space(search_ptr, alloc->end-search_ptr, foreign.ptr);
        if (!enclosing)
            goto next;
        search_ptr = enclosing;

        if (!looks_like_valid_lisp_pointer_p(foreign.ptr, enclosing))
            goto next;

        next:
        if (live_p) {
            if (scanning_roots_p) {
                alloc->state = 1;
            } else {
                struct foreign_allocation * next = alloc->next;
                dequeue_allocation(&maybe_live_allocations, alloc);
                enqueue_allocation((1 == alloc->state)
                                   ? &live_allocations
                                   : &newly_live_allocations,
                                   alloc);
                alloc->state = 2;
                alloc = next;
                search_ptr = alloc->start;
            }
        }
        NEXT_FOREIGN;
    }

#undef NEXT_FOREIGN
#undef NEXT_ALLOC
    done:
    foreign_pointer_count = 0;
}

static int cmp_foreign_allocation_ptr (const void * a, const void * b)
{
    const struct foreign_allocation * x = a;
    const struct foreign_allocation * y = b;

    if (x->start < y->start)
        return -1;

    if (x->start == y->start)
        return 0;

    return 1;
}

static void sort_gced_allocations ()
{
    struct foreign_allocation * ptr;
    unsigned count = 0, size = 1024, i;
    struct foreign_allocation ** vec;
    all_type_masks = 0;
    if (!maybe_live_allocations)
        return;
    /* Blit the list to a vector */
    vec = successful_malloc(size*sizeof(struct foreign_allocation *));

    ptr = maybe_live_allocations;
    do {
        if (count >= size) {
            vec = realloc(vec, sizeof(struct foreign_allocation *) * size * 2);
            gc_assert(vec);
            size *= 2;
        }

        ptr->state = 0;
        vec[count++] = ptr;
        all_type_masks |= ptr->type;
    } while ((ptr = ptr->next) != maybe_live_allocations);

    /* sort the vector */
    qsort(vec,
          count, sizeof(struct foreign_allocation *),
          cmp_foreign_allocation_ptr);

    gc_assert(count);
    /* And blit the sorted vector back to the list */
    for (i = 0; i < count-1; i++) {
        vec[i]->next = vec[i+1];
        vec[i+1]->prev = vec[i];
    }

    vec[count-1]->next = vec[0];
    vec[0]->prev = vec[count-1];

    maybe_live_allocations = vec[0];

    free(vec);
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
