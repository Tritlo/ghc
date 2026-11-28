/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-1999
 *
 * Weak pointers / finalizers
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"
#include "RtsAPI.h"
#include "RtsFlags.h"

#include "RtsUtils.h"
#include "Weak.h"
#include "Schedule.h"
#include "Prelude.h"
#include "ThreadLabels.h"
#include "Trace.h"
#include "AllocArray.h"

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_FINALIZERS
/* Note [Weak finalizer traversal]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The closure header size depends on the RTS way. Rust reads the callback
 * payload from the link offset. Check the other fields against that offset.
 * At shutdown the scheduler has stopped. The registry can still contain
 * DEAD_WEAK entries whose C finalizers already ran. Skip these entries.
 * Each callback runs with the current task's running_finalizers flag set
 * during the shutdown walk. Read each next link after the callback returns.
 */
#define FINALIZER_FIELD(field, index) \
    (offsetof(StgCFinalizerList, field) == \
     offsetof(StgCFinalizerList, link) + (index) * sizeof(void *))
GHC_STATIC_ASSERT(FINALIZER_FIELD(fptr, 1) && FINALIZER_FIELD(ptr, 2) &&
                  FINALIZER_FIELD(eptr, 3) && FINALIZER_FIELD(flag, 4),
                  "Rust C finalizer payload layout");
GHC_STATIC_ASSERT(sizeof(((StgCFinalizerList *)0)->flag) == sizeof(size_t),
                  "Rust C finalizer flag must fit in a native word");
GHC_STATIC_ASSERT(offsetof(StgWeak, header.info) == 0, "Rust weak info pointer layout");
RTS_PRIVATE void ghc_rust_run_c_finalizers(StgCFinalizerList *list, size_t payload_offset);
RTS_PRIVATE void ghc_rust_run_all_c_finalizers(StgWeak *list, bool *running,
    size_t callbacks_offset, size_t link_offset, size_t payload_offset);
RTS_PRIVATE void ghc_rust_schedule_finalizers(Capability *cap, StgWeak *list,
    uint32_t stack_size, CostCentreStack *ccs, size_t link_offset,
    size_t payload_offset, StgClosure *(*runner)(void),
    void (*prepare_header)(StgWeak *), void (*trace_batch)(StgWord));
RTS_PRIVATE StgWord ghc_rust_pending_finalizers(void);
RTS_PRIVATE bool ghc_rust_run_some_finalizers(bool all,
    size_t callbacks_offset, size_t link_offset, size_t payload_offset,
    bool *(*running_flag)(void), void (*trace_begin)(StgWord),
    void (*trace_end)(StgWord));
GHC_STATIC_ASSERT(offsetof(StgWeak, finalizer) + sizeof(void *) ==
                  offsetof(StgWeak, link), "Rust weak finalizer offset");
GHC_STATIC_ASSERT(sizeof(StgWord) == sizeof(size_t), "Rust pending count width");
GHC_STATIC_ASSERT(sizeof(HsInt) == sizeof(StgWord), "Rust finalizer count HsInt width");
GHC_STATIC_ASSERT(sizeof(RtsFlags.GcFlags.initialStkSize) == sizeof(uint32_t),
                  "Rust finalizer stack size width");
GHC_STATIC_ASSERT(sizeof(((Task *)0)->running_finalizers) == sizeof(bool),
                  "Rust finalizer task flag width");
#endif

/* Note [Weak finalizer producer]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The GC owns the new weak list when it calls scheduleFinalizers. Under the
 * nonmoving collector, an older list can still wait for the idle drain.
 * Rust appends the new list with a sequentially consistent store. It counts
 * and marks only the new list, then adds its length to the pending count.
 * The C callback keeps the assertion and profiling header update in the
 * native RTS way. Rust stores the DEAD_WEAK info after that callback.
 */
#if defined(USE_RUST_FINALIZERS) && (defined(ASSERTS_ENABLED) || defined(PROFILING))
static void
prepareDeadWeakHeader(StgWeak *w)
{
    ASSERT(w->header.info != &stg_DEAD_WEAK_info);
#if defined(PROFILING)
    SET_PROF_HDR((StgClosure *)w, w->header.prof.ccs);
#endif
}
#define PREPARE_DEAD_WEAK_HEADER prepareDeadWeakHeader
#else
#define PREPARE_DEAD_WEAK_HEADER NULL
#endif

#if defined(USE_RUST_FINALIZERS) && defined(DEBUG)
static void traceFinalizerBatch(StgWord count)
{
    debugTrace(DEBUG_weak, "weak: batching %" FMT_Word " finalizers", count);
}
#define TRACE_FINALIZER_BATCH traceFinalizerBatch
#else
#define TRACE_FINALIZER_BATCH NULL
#endif

#if defined(USE_RUST_FINALIZERS)
static StgClosure *finalizerBatchRunner(void)
{
    return (StgClosure *)runFinalizerBatch_closure;
}
#endif

/* Note [Weak finalizer queue ownership]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Rust owns the queue head, count, and drain lock in the Rust RTS. The GC
 * appends and marks only the new list. The idle worker holds the drain lock
 * while it runs C callbacks. Rust sets and clears the current task's flag.
 * C supplies the flag address and debug trace hooks.
 */
#if !defined(USE_RUST_FINALIZERS)
// List of dead weak pointers collected by the last GC
static StgWeak *finalizer_list = NULL;

// Use the same count width as the heap array that holds the finalizers.
static StgWord n_finalizers = 0;
#endif

void
runCFinalizers(StgCFinalizerList *list)
{
#if defined(USE_RUST_FINALIZERS)
    ghc_rust_run_c_finalizers(list, offsetof(StgCFinalizerList, link));
#else
    StgCFinalizerList *head;
    for (head = list;
        (StgClosure *)head != &stg_NO_FINALIZER_closure;
        head = (StgCFinalizerList *)head->link)
    {
        if (head->flag)
            ((void (*)(void *, void *))head->fptr)(head->eptr, head->ptr);
        else
            ((void (*)(void *))head->fptr)(head->ptr);
    }
#endif
}

void
runAllCFinalizers(StgWeak *list)
{
    Task *task = myTask();
#if defined(USE_RUST_FINALIZERS)
    ghc_rust_run_all_c_finalizers(list, task ? &task->running_finalizers : NULL,
        offsetof(StgWeak, cfinalizers), offsetof(StgWeak, link),
        offsetof(StgCFinalizerList, link));
#else
    StgWeak *w;
    if (task != NULL) {
        task->running_finalizers = true;
    }

    for (w = list; w; w = w->link) {
        // We need to filter out DEAD_WEAK objects, because it's not guaranteed
        // that the list will not have them when shutting down.
        // They only get filtered out during GC for the generation they
        // belong to.
        // If there's no major GC between the time that the finalizer for the
        // object from the oldest generation is manually called and shutdown
        // we end up running the same finalizer twice. See #7170.
        const StgInfoTable *winfo = ACQUIRE_LOAD(&w->header.info);
        if (winfo != &stg_DEAD_WEAK_info) {
            runCFinalizers((StgCFinalizerList *)w->cfinalizers);
        }
    }

    if (task != NULL) {
        task->running_finalizers = false;
    }
#endif
}

/*
 * scheduleFinalizers() is called on the list of weak pointers found
 * to be dead after a garbage collection.  It overwrites each object
 * with DEAD_WEAK, and creates a new thread to run the pending finalizers.
 *
 * This function is called just after GC.  The weak pointers on the
 * argument list are those whose keys were found to be not reachable,
 * however the value and finalizer fields have by now been marked live.
 * The weak pointer object itself may not be alive - i.e. we may be
 * looking at either an object in from-space or one in to-space.  It
 * doesn't really matter either way.
 *
 * Pre-condition: sched_mutex _not_ held.
 */

void
scheduleFinalizers(Capability *cap, StgWeak *list)
{
#if !defined(USE_RUST_FINALIZERS)
    StgTSO *t;
    StgWord n;
    StgWeak *w;
    StgWord i;
#endif

    // n_finalizers is not necessarily zero under non-moving collection
    // because non-moving collector does not wait for the list to be consumed
    // (by doIdleGcWork()) before appending the list with more finalizers.
#if defined(USE_RUST_FINALIZERS)
    ASSERT(RtsFlags.GcFlags.useNonmoving || ghc_rust_pending_finalizers() == 0);
    ghc_rust_schedule_finalizers(cap, list, RtsFlags.GcFlags.initialStkSize,
        CCS_SYSTEM_OR_NULL, offsetof(StgWeak, link),
        offsetof(StgMutArrPtrs, payload),
        finalizerBatchRunner,
        PREPARE_DEAD_WEAK_HEADER, TRACE_FINALIZER_BATCH);
#else
    ASSERT(RtsFlags.GcFlags.useNonmoving || SEQ_CST_LOAD(&n_finalizers) == 0);

    // Append finalizer_list with the new list. TODO: Perhaps cache tail of the
    // list for faster append. NOTE: We can't append `list` here! Otherwise we
    // end up traversing already visited weaks in the loops below.
    StgWeak **tl = &finalizer_list;
    while (*tl) {
        tl = &(*tl)->link;
    }
    SEQ_CST_STORE(tl, list);

    // Traverse the list and
    //  * count the number of Haskell finalizers
    //  * overwrite all the weak pointers with DEAD_WEAK
    n = 0;
    i = 0;
    for (w = list; w; w = w->link) {
        // Better not be a DEAD_WEAK at this stage; the garbage
        // collector removes DEAD_WEAKs from the weak pointer list.
        ASSERT(w->header.info != &stg_DEAD_WEAK_info);

        if (w->finalizer != &stg_NO_FINALIZER_closure) {
            n++;
        }

        // Remember the length of the list, for runSomeFinalizers() below
        i++;

#if defined(PROFILING)
        // A weak pointer is inherently used, so we do not need to call
        // LDV_recordDead().
        //
        // Furthermore, when PROFILING is turned on, dead weak
        // pointers are exactly as large as weak pointers, so there is
        // no need to fill the slop, either.  See stg_DEAD_WEAK_info
        // in StgMiscClosures.cmm.
#endif

        // We must overwrite the header with DEAD_WEAK, so that if
        // there's a later call to finalizeWeak# on this weak pointer,
        // we don't run the finalizer again.
        SET_HDR(w, &stg_DEAD_WEAK_info, w->header.prof.ccs);
    }

    SEQ_CST_ADD(&n_finalizers, i);

    // No Haskell finalizers to run?
    if (n == 0) return;

    debugTrace(DEBUG_weak, "weak: batching %" FMT_Word " finalizers", n);

    StgMutArrPtrs *arr = allocateMutArrPtrs(cap, n, NULL, CCS_SYSTEM_OR_NULL);
    if (RTS_UNLIKELY(arr == NULL)) exitHeapOverflow();
    // No write barrier needed here; this array is only going to referred to by this core.
    SET_INFO((StgClosure *) arr, &stg_MUT_ARR_PTRS_FROZEN_CLEAN_info);

    n = 0;
    for (w = list; w; w = w->link) {
        if (w->finalizer != &stg_NO_FINALIZER_closure) {
            arr->payload[n] = w->finalizer;
            n++;
        }
    }
    // set all the cards to 1
    StgWord size = n + mutArrPtrsCardTableSize(n);
    // TODO: does this need to be a StgMutArrPtrs with a card table?
    // If the cards are all 1 and the array is clean, couldn't it
    // be a StgSmallMutArrPtrs instead?
    for (i = n; i < size; i++) {
        arr->payload[i] = (StgClosure *)(W_)(-1);
    }

    t = createIOThread(cap,
                       RtsFlags.GcFlags.initialStkSize,
                       rts_apply(cap,
                           rts_apply(cap,
                               (StgClosure *)runFinalizerBatch_closure,
                               rts_mkInt(cap,n)),
                           (StgClosure *)arr)
        );

    scheduleThread(cap,t);
#endif
}

/* -----------------------------------------------------------------------------
   Incrementally running C finalizers

   The GC detects all the dead finalizers, but we don't want to run
   them during the GC because that increases the time that the runtime
   is paused.

   What options are there?

   1. Parallelise running the C finalizers across the GC threads
      - doesn't solve the pause problem, just reduces it (maybe by a lot)

   2. Make a Haskell thread to run the C finalizers, like we do for
      Haskell finalizers.
      + scheduling is handled for us
      - no guarantee that we'll process finalizers in a timely manner

   3. Run finalizers when any capability is idle.
      + reduces pause to 0
      - requires scheduler modifications
      - if the runtime is busy, finalizers wait until the next GC

   4. like (3), but also run finalizers incrementally between GCs.
      - reduces the delay to run finalizers compared with (3)

   For now we do (3). It would be easy to do (4) later by adding a
   call to doIdleGCWork() in the scheduler loop, but I haven't found
   that necessary so far.

   -------------------------------------------------------------------------- */

// Run this many finalizers before returning from
// runSomeFinalizers(). This is so that we only tie up the capability
// for a short time, and respond quickly if new work becomes
// available.
#if !defined(USE_RUST_FINALIZERS)
static const StgWord finalizer_chunk = 100;
#endif

#if defined(USE_RUST_FINALIZERS)
static bool *currentFinalizerRunningFlag(void)
{
    Task *task = myTask();
    return task ? &task->running_finalizers : NULL;
}

#if defined(DEBUG)
static void traceFinalizerDrainBegin(StgWord pending)
{
    debugTrace(DEBUG_sched, "running C finalizers, %" FMT_Word " remaining", pending);
}

static void traceFinalizerDrainEnd(StgWord count)
{
    debugTrace(DEBUG_sched, "ran %" FMT_Word " C finalizers", count);
}
#define TRACE_FINALIZER_DRAIN_BEGIN traceFinalizerDrainBegin
#define TRACE_FINALIZER_DRAIN_END traceFinalizerDrainEnd
#else
#define TRACE_FINALIZER_DRAIN_BEGIN NULL
#define TRACE_FINALIZER_DRAIN_END NULL
#endif
#endif

// non-zero if a thread is already in runSomeFinalizers(). This
// protects the globals finalizer_list and n_finalizers.
#if !defined(USE_RUST_FINALIZERS)
static volatile StgWord finalizer_lock = 0;
#endif

//
// Run some C finalizers.  Returns true if there's more work to do.
//
bool runSomeFinalizers(bool all)
{
#if defined(USE_RUST_FINALIZERS)
    return ghc_rust_run_some_finalizers(all,
        offsetof(StgWeak, cfinalizers), offsetof(StgWeak, link),
        offsetof(StgCFinalizerList, link), currentFinalizerRunningFlag,
        TRACE_FINALIZER_DRAIN_BEGIN, TRACE_FINALIZER_DRAIN_END);
#else
    if (RELAXED_LOAD(&n_finalizers) == 0)
        return false;

    if (cas(&finalizer_lock, 0, 1) != 0) {
        // another capability is doing the work, it's safe to say
        // there's nothing to do, because the thread already in
        // runSomeFinalizers() will call in again.
        return false;
    }

    debugTrace(DEBUG_sched, "running C finalizers, %" FMT_Word " remaining", n_finalizers);

    Task *task = myTask();
    if (task != NULL) {
        task->running_finalizers = true;
    }

    StgWeak *w = finalizer_list;
    StgWord count = 0;
    while (w != NULL) {
        runCFinalizers((StgCFinalizerList *)w->cfinalizers);
        w = w->link;
        ++count;
        if (!all && count >= finalizer_chunk) break;
    }
    RELAXED_STORE(&finalizer_list, w);
    SEQ_CST_ADD(&n_finalizers, -count);

    if (task != NULL) {
        task->running_finalizers = false;
    }

    debugTrace(DEBUG_sched, "ran %" FMT_Word " C finalizers", count);
    bool ret = n_finalizers != 0;
    RELEASE_STORE(&finalizer_lock, 0);
    return ret;
#endif
}
