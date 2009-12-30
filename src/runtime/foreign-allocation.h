#ifndef __FOREIGN_ALLOCATION_H__
#define __FOREIGN_ALLOCATION_H__

#include "runtime.h"

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

extern struct foreign_allocation * always_live_allocations;
extern struct foreign_allocation * dead_allocations;
extern struct foreign_allocation * maybe_live_allocations;
extern struct foreign_allocation * live_allocations;

extern int scanning_roots_p;

void enqueue_allocation (struct foreign_allocation ** queue,
                         struct foreign_allocation * allocation);
void dequeue_allocation (struct foreign_allocation ** queue,
                         struct foreign_allocation * allocation);
void splice_allocations (struct foreign_allocation ** dest,
                         struct foreign_allocation * queue);
struct foreign_allocation * pop_allocation (struct foreign_allocation ** queue);

void register_always_live_allocation (struct foreign_allocation * allocation);
void retire_always_live_allocation (struct foreign_allocation * allocation);
void register_gced_allocation (struct foreign_allocation * allocation);
void retire_gced_allocation (struct foreign_allocation * allocation);

void enqueue_foreign_pointer (lispobj * ptr);
void process_foreign_pointers ();

void prepare_foreign_allocations_for_gc (int full_gc_p);
void scavenge_foreign_allocations (struct foreign_allocation * allocations);
void scavenge_teenaged_alloc ();
void mark_foreign_alloc ();
void sweep_allocations ();
#endif
