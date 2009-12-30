#ifndef __FOREIGN_ALLOCATION_H__
#define __FOREIGN_ALLOCATION_H__
#include "runtime.h"

/* Foreign allocation region descriptors. The interface only
 * manipulates pointers; feel free to "subclass".
 **/
struct foreign_allocation {
    struct foreign_allocation * prev;
    struct foreign_allocation * next;
    lispobj * start;
    lispobj * end;
    /* bitmask:
     * bit  |  meaning if set
     *  0   |   any SAP/raw pointer counts
     *  1   |   lisp heap-like
     *  2   |   SAP/raw pointers to head count
     *  3   |   scavenged region
     */
    int type;
    int state;
    /* 0 : dead or in limbo
     * 1 : teenager (live, but only from direct roots)
     * 2 : adult (live, from heap)
     * -1 : always live
     */
};


/* Foreign allocation region interface.
 */
void register_always_live_allocation (struct foreign_allocation * allocation);
void retire_always_live_allocation (struct foreign_allocation * allocation);
void register_gced_allocation (struct foreign_allocation * allocation);
void retire_gced_allocation (struct foreign_allocation * allocation);


extern struct foreign_allocation * always_live_allocations;
extern struct foreign_allocation * dead_allocations;
extern struct foreign_allocation * maybe_live_allocations;
extern struct foreign_allocation * live_allocations;

void enqueue_allocation (struct foreign_allocation ** queue,
                         struct foreign_allocation * allocation);
void dequeue_allocation (struct foreign_allocation ** queue,
                         struct foreign_allocation * allocation);
void splice_allocations (struct foreign_allocation ** dest,
                         struct foreign_allocation * queue);
struct foreign_allocation *
pop_allocation (struct foreign_allocation ** queue);


/* Interface for the GC.
 */
extern unsigned scanning_roots_p;

extern void (*enqueue_lisp_pointer)(lispobj *);
void enqueue_random_pointer (lispobj * ptr);
void enqueue_sap_pointer (void * ptr);

// should that be public?
void process_foreign_pointers ();

void prepare_foreign_allocations_for_gc (int full_gc_p);
void scavenge_foreign_allocations (struct foreign_allocation * allocations);
void scavenge_teenaged_alloc ();
void mark_foreign_alloc ();
void sweep_allocations ();
#endif
