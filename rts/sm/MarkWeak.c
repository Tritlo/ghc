/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 1998-2008
 *
 * Weak pointers and weak-like things in the GC
 *
 * Documentation on the architecture of the Garbage Collector can be
 * found in the online commentary:
 *
 *   https://gitlab.haskell.org/ghc/ghc/wikis/commentary/rts/storage/gc
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"

#include "MarkWeak.h"
#include "GC.h"
#include "GCThread.h"
#include "GCTDecl.h"
#include "Evac.h"
#include "Trace.h"
#include "Schedule.h"
#include "Weak.h"
#include "Storage.h"
#include "Threads.h"

#include "sm/GCUtils.h"
#include "sm/MarkWeak.h"
#include "sm/Sanity.h"

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_WEAK_GC
/* Note [Weak generation traversal from Rust]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * C supplies the generation fields and TSO layout. Rust visits collected
 * generations in order. The C callbacks inspect heap objects and retain
 * the existing GC worker register rules.
 */
typedef struct {
    generation *generations;
    size_t stride;
    size_t old_threads_offset;
    size_t live_weaks_offset;
    size_t old_weaks_offset;
    size_t number_offset;
    uint32_t collected;
    uint32_t oldest;
    bool nonmoving;
} WeakGenerations;

typedef struct {
    StgClosure *(*liveKey)(StgWeak *, const StgInfoTable *);
    StgWeak **(*destination)(StgWeak *, uint32_t *);
    void (*remember)(gc_thread *, StgWeak *, uint32_t);
    void (*trace)(StgWeak *, uint32_t, uint32_t);
} WeakListOps;

static const WeakListOps weakListOps;
static StgTSO **inspectTidyThread(StgTSO **current);

typedef struct {
    size_t stride;
    size_t old_threads_offset;
    size_t live_weaks_offset;
    size_t old_weaks_offset;
    size_t number_offset;
    size_t weak_payload_offset;
    size_t tso_link_offset;
    size_t tso_what_next_offset;
    StgTSO *end_tso;
    StgWord16 killed;
    StgWord16 complete;
    StgTSO **(*inspect_tso)(StgTSO **);
    const WeakListOps *weak_ops;
    void (*check_oldest)(StgWeak **);
} WeakStageLayout;

typedef struct {
    generation *generations;
    uint32_t collected;
    uint32_t oldest;
    bool nonmoving;
    gc_thread *worker;
    StgWeak **dead;
    StgTSO **resurrected;
    uint32_t *evac_gen;
    bool *failed;
    StgWeak **oldest_old_slot;
} WeakStageRun;

static const WeakStageLayout weakStageLayout;
RTS_PRIVATE void ghc_rust_init_weak_generations(generation *gens, size_t stride,
    size_t live_offset, size_t old_offset, uint32_t collected, uint32_t oldest, bool nonmoving);
RTS_PRIVATE bool ghc_rust_traverse_weaks(const WeakStageLayout *layout,
    const WeakStageRun *run);

static WeakGenerations weakGenerationLayout(void)
{
    return (WeakGenerations) {
        generations, weakStageLayout.stride, weakStageLayout.old_threads_offset,
        weakStageLayout.live_weaks_offset, weakStageLayout.old_weaks_offset,
        weakStageLayout.number_offset, N, oldest_gen->no,
        RtsFlags.GcFlags.useNonmoving
    };
}
#endif

/* -----------------------------------------------------------------------------
   Weak Pointers

   traverseWeakPtrList is called possibly many times during garbage
   collection.  It returns a flag indicating whether it did any work
   (i.e. called evacuate on any live pointers).

   Invariant: traverseWeakPtrList is called when the heap is in an
   idempotent state.  That means that there are no pending
   evacuate/scavenge operations.  This invariant helps the weak
   pointer code decide which weak pointers are dead - if there are no
   new live weak pointers, then all the currently unreachable ones are
   dead.

   For generational GC: we don't try to finalize weak pointers in
   older generations than the one we're collecting.

   There are three distinct stages to processing weak pointers:

   - weak_stage == WeakPtrs

     We process all the weak pointers whose keys are alive (evacuate
     their values and finalizers), and repeat until we can find no new
     live keys.  If no live keys are found in this pass, then we
     evacuate the finalizers of all the dead weak pointers in order to
     run them.

   - weak_stage == WeakThreads

     Now, we discover which *threads* are still alive.  Pointers to
     threads from the all_threads and main thread lists are the
     weakest of all: a pointer from the finalizer of a dead weak
     pointer can keep a thread alive.  Any threads found to be unreachable
     are evacuated and placed on the resurrected_threads list so we
     can send them a signal later.

   - weak_stage == WeakDone

     No more evacuation is done.

   -------------------------------------------------------------------------- */

/* Which stage of processing various kinds of weak pointer are we at?
 * (see traverseWeakPtrList() below for discussion).
 */
#if !defined(USE_RUST_WEAK_GC)
typedef enum { WeakPtrs, WeakThreads, WeakDone } WeakStage;
static WeakStage weak_stage;
#endif

#if !defined(USE_RUST_WEAK_GC)
static void    collectDeadWeakPtrs (generation *gen, StgWeak **dead_weak_ptr_list);
static bool resurrectUnreachableThreads (generation *gen, StgTSO **resurrected_threads);
static void tidyThreadList (generation *gen);
static bool tidyWeakList (generation *gen);
#endif

/*
 * Note [Weak pointer processing and the non-moving GC]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * When using the non-moving GC we defer weak pointer processing
 * until the concurrent marking phase as weaks in the non-moving heap may be
 * keyed on objects living in the non-moving generation. To accomplish this
 * initWeakForGC keeps all weak pointers on oldest_gen->weak_ptr_list, where
 * nonmovingCollect will find them. From there they will be moved to
 * nonmoving_old_weak_ptr_list. During the mark loop we will move weaks with
 * reachable keys to nonmoving_weak_ptr_list. At the end of concurrent marking
 * we tidy the weak list (in nonmovingTidyWeakList) and perform another set of
 * marking as necessary, just as is done in tidyWeakList.
 *
 * Note that this treatment takes advantage of the fact that we usually need
 * not worry about Weak#s living in the non-moving heap but being keyed on an
 * object in the moving heap since the Weak# must be strictly older than the
 * key. Such objects would otherwise pose a problem since the non-moving
 * collector would be unable to safely determine the liveness of the key.
 * In the rare case that we *do* see such a key (e.g. in the case of a
 * pinned ByteArray# living in a partially-filled accumulator block)
 * the nonmoving collector assumes that it is live.
 *
 */

/*
 * Prepare the weak object lists for GC. Specifically, reset weak_stage
 * and move all generations' `weak_ptr_list`s to `old_weak_ptr_list`.
 * Weaks with live keys will later be moved back to `weak_ptr_list` by
 * `tidyWeakList`.
 */
void
initWeakForGC(void)
{
#if defined(USE_RUST_WEAK_GC)
    ghc_rust_init_weak_generations(generations, weakStageLayout.stride,
        weakStageLayout.live_weaks_offset, weakStageLayout.old_weaks_offset,
        N, oldest_gen->no, RtsFlags.GcFlags.useNonmoving);
#else
    uint32_t oldest = N;
    if (RtsFlags.GcFlags.useNonmoving && N == oldest_gen->no) {
        // See Note [Weak pointer processing and the non-moving GC].
        oldest = oldest_gen->no - 1;
    }

    for (uint32_t g = 0; g <= oldest; g++) {
        generation *gen = &generations[g];
        gen->old_weak_ptr_list = gen->weak_ptr_list;
        gen->weak_ptr_list = NULL;
    }

    weak_stage = WeakThreads;
#endif
}

/*
 * Walk the weak pointer lists after having finished a round of scavenging,
 * tidying the weak (and possibly thread) lists (depending upon the current
 * weak_stage).
 *
 * Returns true if new live weak pointers were found, implying that another
 * round of scavenging is necessary.
 */
bool
traverseWeakPtrList(StgWeak **dead_weak_ptr_list, StgTSO **resurrected_threads)
{
#if defined(USE_RUST_WEAK_GC)
  WeakStageRun run = { generations, N, oldest_gen->no,
      RtsFlags.GcFlags.useNonmoving, gct, dead_weak_ptr_list,
      resurrected_threads, &gct->evac_gen_no, &gct->failed_to_evac,
      &oldest_gen->old_weak_ptr_list };
  return ghc_rust_traverse_weaks(&weakStageLayout, &run);
#else
  bool flag = false;

  switch (weak_stage) {

  case WeakDone:
      return false;

  case WeakThreads:
      /* Now deal with the gen->threads lists, which behave somewhat like
       * the weak ptr list.  If we discover any threads that are about to
       * become garbage, we wake them up and administer an exception.
       */
  {
      uint32_t g;

      for (g = 0; g <= N; g++) {
          tidyThreadList(&generations[g]);
      }

      // Use weak pointer relationships (value is reachable if
      // key is reachable):
      for (g = 0; g <= N; g++) {
          if (tidyWeakList(&generations[g])) {
              flag = true;
          }
      }

      // if we evacuated anything new, we must scavenge thoroughly
      // before we can determine which threads are unreachable.
      if (flag) return true;

      // Resurrect any threads which were unreachable
      for (g = 0; g <= N; g++) {
          if (resurrectUnreachableThreads(&generations[g], resurrected_threads)) {
              flag = true;
          }
      }

      // Next, move to the WeakPtrs stage after fully
      // scavenging the finalizers we've just evacuated.
      weak_stage = WeakPtrs;

      // if we evacuated anything new, we must scavenge thoroughly
      // before entering the WeakPtrs stage.
      if (flag) return true;

      // otherwise, fall through...
  }
  FALLTHROUGH;

  case WeakPtrs:
  {
      uint32_t g;

      // resurrecting threads might have made more weak pointers
      // alive, so traverse those lists again:
      for (g = 0; g <= N; g++) {
          if (tidyWeakList(&generations[g])) {
              flag = true;
          }
      }

      /* If we didn't make any changes, then we can go round and kill all
       * the dead weak pointers.  The dead_weak_ptr list is used as a list
       * of pending finalizers later on.
       */
      if (flag == false) {
          for (g = 0; g <= N; g++) {
              collectDeadWeakPtrs(&generations[g], dead_weak_ptr_list);
          }

          weak_stage = WeakDone;  // *now* we're done,
      }

      return true;         // but one more round of scavenging, please
  }

  default:
      barf("traverseWeakPtrList");
      return true;
  }
#endif
}

/*
 * Deal with weak pointers with unreachable keys after GC has concluded.
 * This means marking the finalizer (and possibly value) in preparation for
 * later finalization.
 */
#if defined(USE_RUST_WEAK_GC)
/* Note [Visiting dead weak pointers from Rust]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The main GC thread runs this pass after the weak keys reach a fixed point.
 * Keep each Haskell finalizer alive. A C finalizer also needs the weak value
 * to stay alive until its callback runs. See Note [MallocPtr finalizers] in
 * GHC.Internal.ForeignPtr.
 *
 * Rust passes the addresses of both slots to mark_root. The collector can
 * replace the pointers in these slots. mark_root restores the GC thread
 * register before calling evacuate and restores the caller's register on
 * return. Rust can then link the weak object into the pending list.
 */
// The header size depends on the RTS way. The payload contains five pointers.
#define WEAK_FIELD_OFFSET(field) (offsetof(StgWeak, field) - offsetof(StgWeak, cfinalizers))
GHC_STATIC_ASSERT(WEAK_FIELD_OFFSET(key) == sizeof(void *) &&
                  WEAK_FIELD_OFFSET(value) == 2 * sizeof(void *) &&
                  WEAK_FIELD_OFFSET(finalizer) == 3 * sizeof(void *) &&
                  WEAK_FIELD_OFFSET(link) == 4 * sizeof(void *), "Rust weak payload layout");
#undef WEAK_FIELD_OFFSET
RTS_PRIVATE void ghc_rust_mark_weak_generations(const WeakGenerations *gens, void *gc_thread_ptr,
    size_t payload_offset, void (*check)(StgWeak *));
RTS_PRIVATE void ghc_rust_scavenge_live_weak(StgWeak *w, void *gc_thread_ptr,
    size_t payload_offset);
GHC_STATIC_ASSERT(offsetof(Capability, weak_ptr_list_tl) ==
                  offsetof(Capability, weak_ptr_list_hd) + sizeof(StgWeak *),
                  "Rust capability weak list endpoints");
RTS_PRIVATE void ghc_rust_collect_fresh_weaks(StgWeak **nursery, Capability **caps,
    uint32_t count, size_t endpoints_offset, size_t payload_offset,
    void (*check)(StgWeak *, StgWeak *));
#endif

#if !defined(USE_RUST_WEAK_GC)
static void collectDeadWeakPtrs (generation *gen, StgWeak **dead_weak_ptr_list)
{
    StgWeak *w, *next_w;
    for (w = gen->old_weak_ptr_list; w != NULL; w = next_w) {
        // If we have C finalizers, keep the value alive for this GC.
        // See Note [MallocPtr finalizers] in GHC.ForeignPtr, and #10904
        if (w->cfinalizers != &stg_NO_FINALIZER_closure) {
            evacuate(&w->value);
        }
        evacuate(&w->finalizer);
        next_w = w->link;
        w->link = *dead_weak_ptr_list;
        *dead_weak_ptr_list = w;
    }
}
#endif

/*
 * Deal with threads left on the old_threads list after GC has concluded,
 * moving them onto the resurrected_threads list where appropriate.
 */
#if !defined(USE_RUST_WEAK_GC)
static bool resurrectUnreachableThreads (generation *gen, StgTSO **resurrected_threads)
{
    StgTSO *t, *next;
    bool flag = false;

    for (t = gen->old_threads; t != END_TSO_QUEUE; t = next) {
        next = t->global_link;

        // ThreadFinished and ThreadComplete: we have to keep
        // these on the all_threads list until they
        // become garbage, because they might get
        // pending exceptions.
        switch (t->what_next) {
        case ThreadKilled:
        case ThreadComplete:
            // The thread was unreachable so far, but it might still end up
            // being reachable later, e.g. after collectDeadWeakPtrs(). We don't
            // want the global_link field to be dangling in that case, so reset
            // it to END_TSO_QUEUE. The copying GC doesn't currently care, but
            // the compacting GC does, see #17785.
            t->global_link = END_TSO_QUEUE;
            continue;
        default:
        {
            StgTSO *tmp = t;
            evacuate((StgClosure **)&tmp);
            tmp->global_link = *resurrected_threads;
            *resurrected_threads = tmp;
            flag = true;
        }
        }
    }

    gen->old_threads = END_TSO_QUEUE;
    return flag;
}
#endif

#if defined(USE_RUST_WEAK_GC)
// Rust owns the list links. C supplies the heap layout and mutable-list operations.
static StgClosure *liveWeakKey(StgWeak *w, const StgInfoTable *info)
{
    const StgInfoTable *table = INFO_PTR_TO_STRUCT(info);
    if (table->type != WEAK) {
        barf("tidyWeakList: not WEAK: %d, %p", table->type, w);
    }
    return isAlive(w->key);
}

static StgWeak **weakDestination(StgWeak *w, uint32_t *number)
{
    generation *dest = Bdescr((P_)w)->gen;
    *number = dest->no;
    return &dest->weak_ptr_list;
}

static void rememberUnpromotedWeak(gc_thread *worker USED_IF_THREADS, StgWeak *w, uint32_t gen)
{
#if defined(THREADED_RTS)
    gc_thread *saved = gct;
#endif
    SET_GCT(worker);
    debugTrace(DEBUG_weak, "putting weak pointer %p into mutable list", w);
    gct->failed_to_evac = false;
    recordMutableGen_GC((StgClosure *)w, gen);
    SET_GCT(saved);
}

#if defined(DEBUG)
static void traceLiveWeak(StgWeak *w, uint32_t from, uint32_t to)
{
    if (from != to) {
        debugTrace(DEBUG_weak, "moving weak pointer %p from %d to %d", w, from, to);
    }
    debugTrace(DEBUG_weak, "weak pointer still alive at %p -> %p", w, w->key);
}
#define TRACE_LIVE_WEAK traceLiveWeak
#else
#define TRACE_LIVE_WEAK NULL
#endif

static const WeakListOps weakListOps = {
    liveWeakKey, weakDestination, rememberUnpromotedWeak, TRACE_LIVE_WEAK
};

#if defined(ASSERTS_ENABLED)
static void checkOldestWeakList(StgWeak **slot)
{
    ASSERT(*slot == NULL);
}
#define CHECK_OLDEST_WEAK_LIST checkOldestWeakList
#else
#define CHECK_OLDEST_WEAK_LIST NULL
#endif

static const WeakStageLayout weakStageLayout = {
    sizeof(generation), offsetof(generation, old_threads),
    offsetof(generation, weak_ptr_list), offsetof(generation, old_weak_ptr_list),
    offsetof(generation, no), offsetof(StgWeak, cfinalizers),
    offsetof(StgTSO, global_link), offsetof(StgTSO, what_next),
    END_TSO_QUEUE, ThreadKilled, ThreadComplete,
    inspectTidyThread, &weakListOps, CHECK_OLDEST_WEAK_LIST
};
#undef CHECK_OLDEST_WEAK_LIST
#endif

#if !defined(USE_RUST_WEAK_GC)
/*
 * Walk over the `old_weak_ptr_list` of the given generation and:
 *
 *  - remove any DEAD_WEAKs
 *  - move any weaks with reachable keys to the `weak_ptr_list` of the
 *    appropriate to-space and mark the weak's value and finalizer.
 */
static bool tidyWeakList(generation *gen)
{
    if (RtsFlags.GcFlags.useNonmoving && gen == oldest_gen) {
        // See Note [Weak pointer processing and the non-moving GC].
        ASSERT(gen->old_weak_ptr_list == NULL);
        return false;
    }

    StgWeak *w, **last_w, *next_w;
    const StgInfoTable *info;
    StgClosure *new;
    bool flag = false;
    last_w = &gen->old_weak_ptr_list;
    for (w = gen->old_weak_ptr_list; w != NULL; w = next_w) {

        info = w->header.info;
        /* N.B. This function is executed only during the serial part of GC
         * so consequently there is no potential for data races and therefore
         * no need for memory barriers.
         */

        /* There might be a DEAD_WEAK on the list if finalizeWeak# was
         * called on a live weak pointer object.  Just remove it.
         */
        if (info == &stg_DEAD_WEAK_info) {
            next_w = w->link;
            *last_w = next_w;
            continue;
        }

        info = INFO_PTR_TO_STRUCT(info);
        switch (info->type) {

        case WEAK:
            /* Now, check whether the key is reachable.
             */
            new = isAlive(w->key);
            if (new != NULL) {
                generation *new_gen;

                w->key = new;

                // Find out which generation this weak ptr is in, and
                // move it onto the weak ptr list of that generation.

                new_gen = Bdescr((P_)w)->gen;
                gct->evac_gen_no = new_gen->no;
                gct->failed_to_evac = false;

                // evacuate the fields of the weak ptr
                scavengeLiveWeak(w);

                if (gct->failed_to_evac) {
                    debugTrace(DEBUG_weak,
                               "putting weak pointer %p into mutable list",
                               w);
                    gct->failed_to_evac = false;
                    recordMutableGen_GC((StgClosure *)w, new_gen->no);
                }

                // remove this weak ptr from the old_weak_ptr list
                *last_w = w->link;
                next_w  = w->link;

                // and put it on the correct weak ptr list.
                w->link = new_gen->weak_ptr_list;
                new_gen->weak_ptr_list = w;
                flag = true;

                if (gen->no != new_gen->no) {
                    debugTrace(DEBUG_weak,
                      "moving weak pointer %p from %d to %d",
                      w, gen->no, new_gen->no);
                }


                debugTrace(DEBUG_weak,
                           "weak pointer still alive at %p -> %p",
                           w, w->key);
                continue;
            }
            else {
                last_w = &(w->link);
                next_w = w->link;
                continue;
            }

        default:
            barf("tidyWeakList: not WEAK: %d, %p", info->type, w);
        }
    }

    return flag;
}
#endif

/*
 * Walk over the given generation's thread list and promote TSOs which are
 * reachable via the heap. This will move the TSO from gen->old_threads to
 * new_gen->threads.
 *
 * This has the side-effect of updating the global thread list to account for
 * indirections introduced by evacuation.
 */
/* Note [Tidy thread list ownership]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * isAlive can return a relocated TSO. The C callback updates the pointer
 * and finds its destination generation. Rust reads the next link from
 * that TSO and updates the old list and the destination list. The callback
 * uses isAlive from GCAux.c, which does not use the gct register.
 */
#if defined(USE_RUST_WEAK_GC)
static StgTSO **inspectTidyThread(StgTSO **current)
{
    StgTSO *t = *current;
    StgTSO *live = (StgTSO *)isAlive((StgClosure *)t);
    if (live != NULL) t = live;

    ASSERT(get_itbl((StgClosure *)t)->type == TSO);
    ASSERT(t->blocked_exceptions == END_BLOCKED_EXCEPTIONS_QUEUE
           || t->why_blocked == BlockedOnCCall
           || t->why_blocked == BlockedOnCCall_Interruptible
           || (t->flags & TSO_BLOCKEX));

    *current = t;
    return live != NULL ? &Bdescr((P_)t)->gen->threads : NULL;
}
#endif

#if !defined(USE_RUST_WEAK_GC)
static void tidyThreadList (generation *gen)
{
    StgTSO *next;
    StgTSO **prev = &gen->old_threads;

    for (StgTSO *t = gen->old_threads; t != END_TSO_QUEUE; t = next) {

        StgTSO *tmp = (StgTSO *)isAlive((StgClosure *)t);

        if (tmp != NULL) {
            t = tmp;
        }

        ASSERT(get_itbl((StgClosure *)t)->type == TSO);
        next = t->global_link;

        // if the thread is not masking exceptions but there are
        // pending exceptions on its queue, then something has gone
        // wrong.  However, pending exceptions are OK if there is an
        // FFI call.
        ASSERT(t->blocked_exceptions == END_BLOCKED_EXCEPTIONS_QUEUE
               || t->why_blocked == BlockedOnCCall
               || t->why_blocked == BlockedOnCCall_Interruptible
               || (t->flags & TSO_BLOCKEX));

        if (tmp == NULL) {
            // not alive (yet): leave this thread on the
            // old_threads list.
            prev = &(t->global_link);
        }
        else {
            // alive
            *prev = next;

            // move this thread onto the correct threads list.
            generation *new_gen = Bdescr((P_)t)->gen;
            t->global_link = new_gen->threads;
            new_gen->threads = t;
        }
    }
}
#endif

#if defined(DEBUG)
static void checkWeakPtrSanity(StgWeak *hd, StgWeak *tl)
{
    StgWeak *w, *prev;
    for (prev = NULL, w = hd; w != NULL; prev = w, w = w->link) {
        ASSERT(INFO_PTR_TO_STRUCT(UNTAG_CLOSURE((StgClosure*)w)->header.info)->type == WEAK
            || UNTAG_CLOSURE((StgClosure*)w)->header.info == &stg_DEAD_WEAK_info);
        checkClosure((StgClosure*)w);
    }
    if (tl != NULL) {
        ASSERT(prev == tl);
    }
}
#endif

/*
 * Traverse the capabilities' local new-weak-pointer lists at the beginning of
 * GC and move them to the nursery's weak_ptr_list.
 */
#if defined(USE_RUST_WEAK_GC) && defined(ASSERTS_ENABLED)
static void checkFreshWeakList(StgWeak *head, StgWeak *tail)
{
    if (tail == NULL) {
        ASSERT(head == NULL);
    } else {
        IF_DEBUG(sanity, checkWeakPtrSanity(head, tail));
    }
}
#define CHECK_FRESH_WEAK_LIST checkFreshWeakList
#else
#define CHECK_FRESH_WEAK_LIST NULL
#endif

void collectFreshWeakPtrs( void )
{
#if defined(USE_RUST_WEAK_GC)
    // GC owns all capability lists until scavenging starts.
    ghc_rust_collect_fresh_weaks(&g0->weak_ptr_list, capabilities, getNumCapabilities(),
        offsetof(Capability, weak_ptr_list_hd), offsetof(StgWeak, cfinalizers),
        CHECK_FRESH_WEAK_LIST);
#else
    uint32_t i;
    // move recently allocated weak_ptr_list to the old list as well
    for (i = 0; i < getNumCapabilities(); i++) {
        Capability *cap = getCapability(i);
        if (cap->weak_ptr_list_tl != NULL) {
            IF_DEBUG(sanity, checkWeakPtrSanity(cap->weak_ptr_list_hd, cap->weak_ptr_list_tl));
            cap->weak_ptr_list_tl->link = g0->weak_ptr_list;
            g0->weak_ptr_list = cap->weak_ptr_list_hd;
            cap->weak_ptr_list_tl = NULL;
            cap->weak_ptr_list_hd = NULL;
        } else {
            ASSERT(cap->weak_ptr_list_hd == NULL);
        }
    }
#endif
}

/* -----------------------------------------------------------------------------
   Evacuate every weak pointer object on the weak_ptr_list, and update
   the link fields.
   -------------------------------------------------------------------------- */

#if defined(ASSERTS_ENABLED)
static inline void checkWeakBeforeEvacuation(StgWeak *w)
{
    // A parallel worker can replace the info pointer with a forwarding pointer.
    const StgInfoTable *info = RELAXED_LOAD(&w->header.info);
    ASSERT(IS_FORWARDING_PTR(info)
           || info == &stg_DEAD_WEAK_info
           || INFO_PTR_TO_STRUCT(info)->type == WEAK);
}
#define CHECK_WEAK_BEFORE_EVACUATION checkWeakBeforeEvacuation
#else
#define CHECK_WEAK_BEFORE_EVACUATION NULL
#endif

void
markWeakPtrList ( void )
{
#if defined(USE_RUST_WEAK_GC)
    WeakGenerations gens = weakGenerationLayout();
    ghc_rust_mark_weak_generations(&gens, gct, offsetof(StgWeak, cfinalizers),
                                   CHECK_WEAK_BEFORE_EVACUATION);
#else
    for (uint32_t g = 0; g <= N; g++) {
        generation *gen = &generations[g];
        StgWeak *w, **last_w;

        last_w = &gen->weak_ptr_list;
        for (w = gen->weak_ptr_list; w != NULL; w = RELAXED_LOAD(&w->link)) {
            // w might be WEAK, EVACUATED, or DEAD_WEAK (actually CON_STATIC) here

#if defined(ASSERTS_ENABLED)
            checkWeakBeforeEvacuation(w);
#endif

            evacuate((StgClosure **)last_w);
            w = *last_w;
            last_w = &(w->link);
        }
    }
#endif
}

/* -----------------------------------------------------------------------------
   Fully scavenge a known-to-be-alive weak pointer.

   In scavenge_block, we only partially scavenge a weak pointer because it may
   turn out to be dead. This function should be called when we decide that the
   weak pointer is alive after this GC.
   -------------------------------------------------------------------------- */

void
scavengeLiveWeak(StgWeak *w)
{
#if defined(USE_RUST_WEAK_GC)
    ghc_rust_scavenge_live_weak(w, gct, offsetof(StgWeak, cfinalizers));
#else
    evacuate(&w->value);
    evacuate(&w->key);
    evacuate(&w->finalizer);
    evacuate(&w->cfinalizers);
#endif
}

#if defined(USE_RUST_WEAK_GC)
/* Note [Live weak roots from Rust]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Rust selects the four writable fields and their visit order. Install the
 * GC worker once while C evacuates those fields. Each slot can change.
 */
RTS_PRIVATE void ghc_rust_mark_weak_roots(gc_thread *worker USED_IF_THREADS,
    StgClosure **value, StgClosure **key, StgClosure **finalizer,
    StgClosure **cfinalizers)
{
#if defined(THREADED_RTS)
    gc_thread *saved = gct;
#endif
    SET_GCT(worker);
    evacuate(value);
    evacuate(key);
    evacuate(finalizer);
    evacuate(cfinalizers);
    SET_GCT(saved);
}
#endif
