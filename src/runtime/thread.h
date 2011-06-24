#if !defined(_INCLUDE_THREAD_H_)
#define _INCLUDE_THREAD_H_

#include <sys/types.h>
#include <unistd.h>
#include <stddef.h>
#include "sbcl.h"
#include "globals.h"
#include "runtime.h"
#include "os.h"
#ifdef LISP_FEATURE_GENCGC
#include "gencgc-alloc-region.h"
#else
struct alloc_region { };
#endif
#include "genesis/symbol.h"
#include "genesis/static-symbols.h"
#include "genesis/thread.h"
#include "genesis/fdefn.h"
#include "interrupt.h"
#include "validate.h"           /* for BINDING_STACK_SIZE etc */

#define STATE_RUNNING (make_fixnum(1))
#define STATE_SUSPENDED (make_fixnum(2))
#define STATE_DEAD (make_fixnum(3))
#if defined(LISP_FEATURE_SB_SAFEPOINT)
#define STATE_SUSPENDED_BRIEFLY (make_fixnum(4))
#define STATE_GC_BLOCKER (make_fixnum(5))
#define STATE_PHASE1_BLOCKER (make_fixnum(5))
#define STATE_PHASE2_BLOCKER (make_fixnum(6))
#define STATE_INTERRUPT_BLOCKER (make_fixnum(7))
#endif

#if defined(LISP_FEATURE_SB_SAFEPOINT)
enum threads_suspend_reason {
    SUSPEND_REASON_NONE,
    SUSPEND_REASON_GC,
    SUSPEND_REASON_INTERRUPT,
    SUSPEND_REASON_GCING
};

struct threads_suspend_info {
    int suspend;
    pthread_mutex_t world_lock;
    pthread_mutex_t lock;
    enum threads_suspend_reason reason;
    int phase;
    struct thread * gc_thread;
    struct thread * interrupted_thread;
    int blockers;
    int used_gc_page;
};

struct suspend_phase {
    int suspend;
    enum threads_suspend_reason reason;
    int phase;
    struct suspend_phase *next;
};

extern struct threads_suspend_info suspend_info;

struct gcing_safety {
    lispobj csp_around_foreign_call;
    lispobj* pc_around_foreign_call;
};

int handle_safepoint_violation(os_context_t *context, os_vm_address_t addr);
void** os_get_csp(struct thread* th);
void alloc_gc_page();
void assert_on_stack(struct thread *th, void *esp);
#endif

#ifdef LISP_FEATURE_SB_THREAD
/* Only access thread state with blockables blocked. */
static inline lispobj
thread_state(struct thread *thread)
{
    lispobj state;
    pthread_mutex_lock(thread->state_lock);
    state = thread->state;
    pthread_mutex_unlock(thread->state_lock);
    return state;
}

#if defined(LISP_FEATURE_SB_SAFEPOINT)
static const char *
get_thread_state_string(lispobj state)
{
    if (state == STATE_RUNNING) return "RUNNING";
    if (state == STATE_SUSPENDED) return "SUSPENDED";
    if (state == STATE_DEAD) return "DEAD";
    if (state == STATE_SUSPENDED_BRIEFLY) return "SUSPENDED_BRIEFLY";
    if (state == STATE_PHASE1_BLOCKER) return "PHASE1_BLOCKER";
    if (state == STATE_PHASE2_BLOCKER) return "PHASE2_BLOCKER";
    if (state == STATE_INTERRUPT_BLOCKER) return "INTERRUPT_BLOCKER";
    return "unknown";
}

static const char *
get_thread_state_as_string(struct thread * thread)
{
  return get_thread_state_string(thread_state(thread));
}
#endif

static inline void
set_thread_state(struct thread *thread, lispobj state)
{
    pthread_mutex_lock(thread->state_lock);
    thread->state = state;
    /* zzz AK swaps these, not entirely certain why.  Presumably just
     * for performance (lack of wait morphing)?  Are we certain it
     * doesn't affect correctness? */
    pthread_cond_broadcast(thread->state_cond);
    pthread_mutex_unlock(thread->state_lock);
}

static inline void
wait_for_thread_state_change(struct thread *thread, lispobj state)
{
    pthread_mutex_lock(thread->state_lock);
    while (thread->state == state)
        pthread_cond_wait(thread->state_cond, thread->state_lock);
    pthread_mutex_unlock(thread->state_lock);
}

extern pthread_key_t lisp_thread;
#endif

extern int kill_safely(os_thread_t os_thread, int signal);

#define THREAD_SLOT_OFFSET_WORDS(c) \
 (offsetof(struct thread,c)/(sizeof (struct thread *)))

union per_thread_data {
    struct thread thread;
    lispobj dynamic_values[1];  /* actually more like 4000 or so */
};

/* A helper structure for data local to a thread, which is not pointer-sized.
 *
 * Originally, all layouting of these fields was done manually in C code
 * with pointer arithmetic.  We let the C compiler figure it out now.
 *
 * (Why is this not part of `struct thread'?  Because that structure is
 * declared using genesis, and we would run into issues with fields that
 * are of unknown length.)
 */
struct nonpointer_thread_data
{
#ifdef LISP_FEATURE_SB_THREAD
    pthread_mutex_t state_lock;
    pthread_cond_t state_cond;
# ifdef LISP_FEATURE_SB_SAFEPOINT
   /* For safepoint-based builds, together with thread's
    * csp_around_foreign_call pointer target, thread_qrl(thread) makes
    * `quickly revokable lock'. Unlike most mutexes, this one is
    * normally locked; by convention, other thread may read and use the
    * thread's FFI-CSP location _either_ when the former holds the
    * lock(mutex) _or_ when page permissions for FFI-CSP location were
    * set to read-only.
    *
    * Combined semantic of QRL is not the same as the semantic of mutex
    * returned by this function; rather, the mutex, when released by the
    * owning thread, provides an edge-triggered notification of QRL
    * release, which is represented by writing non-null
    * csp_around_foreign_call.
    *
    * When owner thread is `in Lisp' (i.e. a heap mutator), its FFI-CSP
    * contains null, otherwise it points to the top of C stack that
    * should be preserved by GENCGC. If another thread needs to wait for
    * mutator state change with `in Lisp => in C' direction, it disables
    * FFI-CSP overwrite using page protection, and takes the mutex
    * returned by thread_qrl(). Page fault handler normally ends up in a
    * routine releasing this mutex and waiting for some appropriate
    * event to take it back.
    *
    * This way, each thread may modify its own FFI-CSP content freely
    * without memory barriers (paying with exception handling overhead
    * whenever a contention happens). */
    pthread_mutex_t qrl_lock;
# endif
#else
    /* An unused field follows, to ensure that the struct in non-empty
     * for non-GCC compilers. */
    int unused;
#endif
};

extern struct thread *all_threads;
extern int dynamic_values_bytes;

#if defined(LISP_FEATURE_DARWIN)
#define CONTROL_STACK_ALIGNMENT_BYTES 8192 /* darwin wants page-aligned stacks */
#define THREAD_ALIGNMENT_BYTES CONTROL_STACK_ALIGNMENT_BYTES
#else
#define THREAD_ALIGNMENT_BYTES BACKEND_PAGE_BYTES
#define CONTROL_STACK_ALIGNMENT_BYTES 16
#endif


#ifdef LISP_FEATURE_SB_THREAD
#define for_each_thread(th) for(th=all_threads;th;th=th->next)
#else
/* there's some possibility a SSC could notice this never actually
 * loops  */
#define for_each_thread(th) for(th=all_threads;th;th=0)
#endif

static inline lispobj *
SymbolValueAddress(u64 tagged_symbol_pointer, void *thread)
{
    struct symbol *sym= (struct symbol *)
        (pointer_sized_uint_t)(tagged_symbol_pointer-OTHER_POINTER_LOWTAG);
#ifdef LISP_FEATURE_SB_THREAD
    if(thread && sym->tls_index) {
        lispobj *r = &(((union per_thread_data *)thread)
                       ->dynamic_values[fixnum_value(sym->tls_index)]);
        if((*r)!=NO_TLS_VALUE_MARKER_WIDETAG) return r;
    }
#endif
    return &sym->value;
}

static inline lispobj
SymbolValue(u64 tagged_symbol_pointer, void *thread)
{
    struct symbol *sym= (struct symbol *)
        (pointer_sized_uint_t)(tagged_symbol_pointer-OTHER_POINTER_LOWTAG);
#ifdef LISP_FEATURE_SB_THREAD
    if(thread && sym->tls_index) {
        lispobj r=
            ((union per_thread_data *)thread)
            ->dynamic_values[fixnum_value(sym->tls_index)];
        if(r!=NO_TLS_VALUE_MARKER_WIDETAG) return r;
    }
#endif
    return sym->value;
}

static inline lispobj
SymbolTlValue(u64 tagged_symbol_pointer, void *thread)
{
    struct symbol *sym= (struct symbol *)
        (pointer_sized_uint_t)(tagged_symbol_pointer-OTHER_POINTER_LOWTAG);
#ifdef LISP_FEATURE_SB_THREAD
    return ((union per_thread_data *)thread)
        ->dynamic_values[fixnum_value(sym->tls_index)];
#else
    return sym->value;
#endif
}

static inline void
SetSymbolValue(u64 tagged_symbol_pointer,lispobj val, void *thread)
{
    struct symbol *sym= (struct symbol *)
        (pointer_sized_uint_t)(tagged_symbol_pointer-OTHER_POINTER_LOWTAG);
#ifdef LISP_FEATURE_SB_THREAD
    if(thread && sym->tls_index) {
        lispobj *pr= &(((union per_thread_data *)thread)
                       ->dynamic_values[fixnum_value(sym->tls_index)]);
        if(*pr!=NO_TLS_VALUE_MARKER_WIDETAG) {
            *pr=val;
            return;
        }
    }
#endif
    sym->value = val;
}

static inline void
SetTlSymbolValue(u64 tagged_symbol_pointer,lispobj val, void *thread)
{
#ifdef LISP_FEATURE_SB_THREAD
    struct symbol *sym= (struct symbol *)
        (pointer_sized_uint_t)(tagged_symbol_pointer-OTHER_POINTER_LOWTAG);
    ((union per_thread_data *)thread)
        ->dynamic_values[fixnum_value(sym->tls_index)]
        =val;
#else
    SetSymbolValue(tagged_symbol_pointer,val,thread) ;
#endif
}

/* This only works for static symbols. */
static inline lispobj
StaticSymbolFunction(lispobj sym)
{
    return ((struct fdefn *)native_pointer(SymbolValue(sym, 0)))->fun;
}

/* These are for use during GC, on the current thread, or on prenatal
 * threads only. */
#if defined(LISP_FEATURE_SB_THREAD)
#define get_binding_stack_pointer(thread)       \
    ((thread)->binding_stack_pointer)
#define set_binding_stack_pointer(thread,value) \
    ((thread)->binding_stack_pointer = (lispobj *)(value))
#define access_control_stack_pointer(thread) \
    ((thread)->control_stack_pointer)
#  if !defined(LISP_FEATURE_X86) && !defined(LISP_FEATURE_X86_64)
#define access_control_frame_pointer(thread) \
    ((thread)->control_frame_pointer)
#  endif
#elif defined(LISP_FEATURE_X86) || defined(LISP_FEATURE_X86_64)
#define get_binding_stack_pointer(thread)       \
    SymbolValue(BINDING_STACK_POINTER, thread)
#define set_binding_stack_pointer(thread,value) \
    SetSymbolValue(BINDING_STACK_POINTER, (lispobj)(value), thread)
#define access_control_stack_pointer(thread)    \
    (current_control_stack_pointer)
#else
#define get_binding_stack_pointer(thread)       \
    (current_binding_stack_pointer)
#define set_binding_stack_pointer(thread,value) \
    (current_binding_stack_pointer = (lispobj *)(value))
#define access_control_stack_pointer(thread) \
    (current_control_stack_pointer)
#define access_control_frame_pointer(thread) \
    (current_control_frame_pointer)
#endif

#if defined(LISP_FEATURE_SB_THREAD) && defined(LISP_FEATURE_GCC_TLS)
extern __thread struct thread *current_thread;
#endif

#ifdef LISP_FEATURE_SB_SAFEPOINT
# define THREAD_CSP_PAGE_SIZE BACKEND_PAGE_BYTES
#else
# define THREAD_CSP_PAGE_SIZE 0
#endif

#define THREAD_STRUCT_SIZE (thread_control_stack_size + BINDING_STACK_SIZE + \
                            ALIEN_STACK_SIZE +                          \
                            sizeof(struct nonpointer_thread_data) +     \
                            dynamic_values_bytes +                      \
                            32 * SIGSTKSZ +                             \
                            THREAD_ALIGNMENT_BYTES +                    \
                            THREAD_CSP_PAGE_SIZE)

/* This is clearly per-arch and possibly even per-OS code, but we can't
 * put it somewhere sensible like x86-linux-os.c because it needs too
 * much stuff like struct thread and all_threads to be defined, which
 * usually aren't by that time.  So, it's here instead.  Sorry */

static inline struct thread *arch_os_get_current_thread(void)
{
#if defined(LISP_FEATURE_SB_THREAD)
#if defined(LISP_FEATURE_X86)
    register struct thread *me=0;
    if(all_threads) {
#if defined(LISP_FEATURE_DARWIN) && defined(LISP_FEATURE_RESTORE_FS_SEGMENT_REGISTER_FROM_TLS)
        sel_t sel;
        struct thread *th = pthread_getspecific(specials);
        sel.index = th->tls_cookie;
        sel.rpl = USER_PRIV;
        sel.ti = SEL_LDT;
        __asm__ __volatile__ ("movw %w0, %%fs" : : "r"(sel));
#elif defined(LISP_FEATURE_FREEBSD)
#ifdef LISP_FEATURE_GCC_TLS
        struct thread *th = current_thread;
#else
        struct thread *th = pthread_getspecific(specials);
#endif
#ifdef LISP_FEATURE_RESTORE_TLS_SEGMENT_REGISTER_FROM_TLS
        unsigned int sel = LSEL(th->tls_cookie, SEL_UPL);
        unsigned int fs = rfs();

        /* Load FS only if it's necessary.  Modifying a selector
         * causes privilege checking and it takes long time. */
        if (fs != sel)
            load_fs(sel);
#endif
        return th;
#endif
        __asm__ __volatile__ ("movl %%fs:%c1,%0" : "=r" (me)
                 : "i" (offsetof (struct thread,this)));
    }
    return me;
#else
#ifdef LISP_FEATURE_GCC_TLS
    return current_thread;
#else
    return pthread_getspecific(specials);
#endif
#endif /* x86 */
#else
     return all_threads;
#endif
}

#if defined(LISP_FEATURE_MACH_EXCEPTION_HANDLER)
#define THREAD_STRUCT_TO_EXCEPTION_PORT(th) ((mach_port_t) th)
#define EXCEPTION_PORT_TO_THREAD_STRUCT(th) ((struct thread *) th)
#endif

#ifdef LISP_FEATURE_SB_SAFEPOINT
void thread_in_safety_transition(os_context_t *ctx);
void thread_in_lisp_raised(os_context_t *ctx);
void thread_pitstop(os_context_t *ctxptr);
extern void thread_register_gc_trigger();

#define thread_qrl(th) (&(th)->nonpointer_data->qrl_lock)

static inline
void push_gcing_safety(struct gcing_safety *into)
{
    struct thread* th = arch_os_get_current_thread();
    asm volatile ("");
    if ((into->csp_around_foreign_call =
         *th->csp_around_foreign_call)) {
        *th->csp_around_foreign_call = 0;
        asm volatile ("");
        into->pc_around_foreign_call = th->pc_around_foreign_call;
        th->pc_around_foreign_call = 0;
        asm volatile ("");
    } else {
        into->pc_around_foreign_call = 0;
    }
}

static inline
void pop_gcing_safety(struct gcing_safety *from)
{
    struct thread* th = arch_os_get_current_thread();
    if (from->csp_around_foreign_call) {
        asm volatile ("");
        *th->csp_around_foreign_call = from->csp_around_foreign_call;
        asm volatile ("");
        th->pc_around_foreign_call = from->pc_around_foreign_call;
        asm volatile ("");
    }
}

/* Even with just -O1, gcc optimizes the jumps in this "loop" away
 * entirely, giving the ability to define WITH-FOO-style macros. */
#define RUN_BODY_ONCE(prefix, finally_do)               \
    int prefix##done = 0;                               \
    for (; !prefix##done; finally_do, prefix##done = 1)

#define WITH_GC_AT_SAFEPOINTS_ONLY_hygenic(var)        \
    struct gcing_safety var;                    \
    push_gcing_safety(&var);                    \
    RUN_BODY_ONCE(var, pop_gcing_safety(&var))

#define WITH_GC_AT_SAFEPOINTS_ONLY()                           \
    WITH_GC_AT_SAFEPOINTS_ONLY_hygenic(sbcl__gc_safety)

#endif

extern boolean is_some_thread_local_addr(os_vm_address_t addr);
extern void create_initial_thread(lispobj);

#ifdef LISP_FEATURE_SB_THREAD
extern pthread_mutex_t all_threads_lock;
#endif

#endif /* _INCLUDE_THREAD_H_ */
