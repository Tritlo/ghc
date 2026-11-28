/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2000-2008
 *
 * Sparking support for THREADED_RTS version of the RTS.
 *
 -------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"

#include "Schedule.h"
#include "RtsUtils.h"
#include "Trace.h"
#include "Prelude.h"
#include "Sparks.h"
#include "ThreadLabels.h"
#include "sm/NonMovingMark.h"
#include "rts/storage/HeapAlloc.h"

#if defined(THREADED_RTS)

SparkPool *
allocSparkPool( void )
{
    return newWSDeque(RtsFlags.ParFlags.maxLocalSparks);
}

void
freeSparkPool (SparkPool *pool)
{
    freeWSDeque(pool);
}

/* -----------------------------------------------------------------------------
 *
 * Turn a spark into a real thread
 *
 * -------------------------------------------------------------------------- */

void
createSparkThread (Capability *cap)
{
    StgTSO *tso;

    tso = createIOThread (cap, RtsFlags.GcFlags.initialStkSize,
                          (StgClosure *)runSparks_closure);
    setThreadLabel(cap, tso, "spark evaluator");
    traceEventCreateSparkThread(cap, tso->id);

    appendToRunQueue(cap,tso);
}

/* --------------------------------------------------------------------------
 * newSpark: create a new spark, as a result of calling "par"
 * Called directly from STG.
 * -------------------------------------------------------------------------- */

StgInt
newSpark (StgRegTable *reg, StgClosure *p)
{
    Capability *cap = regTableToCapability(reg);
    SparkPool *pool = cap->sparks;

    if (!fizzledSpark(p)) {
        if (pushWSDeque(pool,p)) {
            cap->spark_stats.created++;
            traceEventSparkCreate(cap);
        } else {
            /* overflowing the spark pool */
            cap->spark_stats.overflowed++;
            traceEventSparkOverflow(cap);
        }
    } else {
        cap->spark_stats.dud++;
        traceEventSparkDud(cap);
    }

    return 1;
}

/* Note [Pruning the spark pool]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
pruneSparkQueue checks if closures have been evacuated to know weither or
not a spark can be GCed. If it was evacuated it's live and we keep the spark
alive. If it hasn't been evacuated at the end of GC we can assume it's dead and
remove the spark from the pool.

To make this sound we must ensure GC has finished evacuating live objects before
we prune the spark pool. Otherwise we might GC a spark before it has been evaluated.

* If we run sequential GC then the GC Lead simply prunes after
everything has been evacuated.

* If we run parallel gc without work stealing then GC workers are not synchronized
at any point before the worker returns. So we leave it to the GC Lead to prune
sparks once evacuation has been finished and all workers returned.

* If work stealing is enabled all GC threads will be running
scavenge_until_all_done until regular heap marking is done. After which
all workers will converge on a synchronization point. This means
we can perform spark pruning inside the GC workers at this point.
The only wart is that if we prune sparks locally we might
miss sparks reachable via weak pointers as these are marked in the main
thread concurrently to the calls to pruneSparkQueue. To fix this problem would
require a GC barrier but that seems to high a price to pay.
*/


/* --------------------------------------------------------------------------
 * Remove all sparks from the spark queues which should not spark any
 * more.  Called after GC. We assume exclusive access to the structure
 * and replace  all sparks in the queue, see explanation below. At exit,
 * the spark pool only contains sparkable closures.
 * -------------------------------------------------------------------------- */

typedef struct {
    Capability *cap;
    bool nonmovingMarkFinished;
    uint32_t pruned_sparks;
} SparkPruning;

// Keep policy here. The deque only decides where to write a retained spark.
STATIC_INLINE StgClosure *
retainSpark(void *user, StgClosure *spark)
{
    SparkPruning *pruning = user;
    Capability *cap = pruning->cap;

    // Another GC thread can evacuate the closure. Read its info pointer once.
    if (GET_CLOSURE_TAG(spark) == 0) {
        const StgInfoTable *info = ACQUIRE_LOAD(&spark->header.info);
        if (IS_FORWARDING_PTR(info)) {
            StgClosure *forwarded = (StgClosure *)UN_FORWARDING_PTR(info);
            if (closure_SHOULD_SPARK(forwarded)) {
                return forwarded;
            }
        } else if (HEAP_ALLOCED(spark)) {
            bdescr *spark_bd = Bdescr((P_)spark);
            bool is_alive;
            if (pruning->nonmovingMarkFinished) {
                // See Note [Spark management under the nonmoving collector]
                // in NonMoving.c.
                is_alive = !(spark_bd->flags & BF_NONMOVING) || nonmovingIsAlive(spark);
            } else {
                is_alive = spark_bd->flags & (BF_EVACUATED | BF_NONMOVING);
            }

            if (!is_alive) {
                pruning->pruned_sparks++;
                cap->spark_stats.gcd++;
                traceEventSparkGC(cap);
                return NULL;
            }
            if (closure_SHOULD_SPARK(spark)) {
                return spark;
            }
        } else if (INFO_PTR_TO_STRUCT(info)->type == THUNK_STATIC) {
            // See Note [STATIC_LINK fields]. isAlive() also ignores statics.
            return spark;
        }
    }

    pruning->pruned_sparks++;
    cap->spark_stats.fizzled++;
    traceEventSparkFizzle(cap);
    return NULL;
}

void
pruneSparkQueue(bool nonmovingMarkFinished, Capability *cap)
{
    SparkPool *pool = cap->sparks;
    SparkPruning pruning = { cap, nonmovingMarkFinished, 0 };

    IF_DEBUG(sparks, {
        StgInt top = stg_min(pool->top, pool->bottom);
        StgInt bottom = pool->bottom - (top & ~pool->moduloSize);
        top &= pool->moduloSize;
        debugTrace(DEBUG_sparks,
                   "markSparkQueue: current spark queue len=%ld; "
                   "(hd=%" FMT_Int "; tl=%" FMT_Int ")",
                   (long)(bottom - top), bottom, top);
    });

    retainWSDequeClosureSlots(pool, retainSpark, &pruning);

    debugTrace(DEBUG_sparks, "pruned %d sparks", pruning.pruned_sparks);
    debugTrace(DEBUG_sparks,
               "new spark queue len=%ld; (hd=%" FMT_Int "; tl=%" FMT_Int ")",
               sparkPoolSize(pool), pool->bottom, pool->top);
    ASSERT_WSDEQUE_INVARIANTS(pool);
}

/* GC for the spark pool, called inside Capability.c for all
   capabilities in turn. Blindly "evac"s complete spark pool. */
void
traverseSparkQueue (evac_fn evac, void *user, Capability *cap)
{
    SparkPool *pool = cap->sparks;
    visitWSDequeClosureSlots(pool, evac, user);

    debugTrace(DEBUG_sparks,
               "traversed spark queue, len=%ld; "
               "(hd=%" FMT_Int "; tl=%" FMT_Int ")",
               sparkPoolSize(pool), pool->bottom, pool->top);
}

#else

StgInt
newSpark (StgRegTable *reg STG_UNUSED, StgClosure *p STG_UNUSED)
{
    /* nothing */
    return 1;
}

#endif /* THREADED_RTS */
