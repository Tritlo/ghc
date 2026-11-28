/* -*- tab-width: 4 -*- */

/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2002
 *
 * Stable pointers
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"
#include "RtsAPI.h"

#include "Hash.h"
#include "RtsUtils.h"
#include "Trace.h"
#include "StablePtr.h"

#include <string.h>

/* Comment from ADR's implementation in old RTS:

  This files (together with @ghc/runtime/storage/PerformIO.lhc@ and a
  small change in @HpOverflow.lc@) consists of the changes in the
  runtime system required to implement "Stable Pointers". But we're
  getting a bit ahead of ourselves --- what is a stable pointer and what
  is it used for?

  When Haskell calls C, it normally just passes over primitive integers,
  floats, bools, strings, etc.  This doesn't cause any problems at all
  for garbage collection because the act of passing them makes a copy
  from the heap, stack or wherever they are onto the C-world stack.
  However, if we were to pass a heap object such as a (Haskell) @String@
  and a garbage collection occurred before we finished using it, we'd run
  into problems since the heap object might have been moved or even
  deleted.

  So, if a C call is able to cause a garbage collection or we want to
  store a pointer to a heap object between C calls, we must be careful
  when passing heap objects. Our solution is to keep a table of all
  objects we've given to the C-world and to make sure that the garbage
  collector collects these objects --- updating the table as required to
  make sure we can still find the object.


  Of course, all this rather begs the question: why would we want to
  pass a boxed value?

  One very good reason is to preserve laziness across the language
  interface. Rather than evaluating an integer or a string because it
  {\em might\/} be required by the C function, we can wait until the C
  function actually wants the value and then force an evaluation.

  Another very good reason (the motivating reason!) is that the C code
  might want to execute an object of sort $IO ()$ for the side-effects
  it will produce. For example, this is used when interfacing to an X
  widgets library to allow a direct implementation of callbacks.

  One final reason is that we may want to store composite Haskell
  values in data structures implemented in the C side. Serializing and
  deserializing these structures into unboxed form suitable for C may
  be more expensive than maintaining the extra layer of indirection of
  stable pointers.

  The @makeStablePointer :: a -> IO (StablePtr a)@ function
  converts a value into a stable pointer.  It is part of the @PrimIO@
  monad, because we want to be sure we don't allocate one twice by
  accident, and then only free one of the copies.

  \begin{verbatim}
  makeStablePtr#  :: a -> State# RealWorld -> (# RealWorld, a #)
  freeStablePtr#  :: StablePtr# a -> State# RealWorld -> State# RealWorld
  deRefStablePtr# :: StablePtr# a -> State# RealWorld ->
        (# State# RealWorld, a #)
  \end{verbatim}

  There may be additional functions on the C side to allow evaluation,
  application, etc of a stable pointer.

  Stable Pointers are exported to the outside world as indices and not
  pointers, because the stable pointer table is allowed to be
  reallocated for growth. The table is never shrunk for its space to
  be reclaimed.

  Future plans for stable ptrs include distinguishing them by the
  generation of the pointed object. See
  https://gitlab.haskell.org/ghc/ghc/issues/7670 for details.
*/

/*
 * Note [NULL StgStablePtr]
 * ~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * StablePtr index 0 is reserved to represent NULL. Consequently, we must
 * subtract 1 to get the index into the array and add 1 to the index to get the
 * StablePtr.
 */


// the global stable pointer entry table
spEntry *stable_ptr_table = NULL;

// the next free stable ptr, the free entries form a linked list where spEntry.addr points to the next after
static spEntry *stable_ptr_free = NULL;

// current stable pointer table size
static unsigned int SPT_size = 0;
#define INIT_SPT_SIZE 64

/* Keep the C atomic operations visible to ThreadSanitizer. */
#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_STABLE_PTR_TABLE 1
RTS_PRIVATE void ghc_rust_init_stable_ptr_table(spEntry **table, spEntry **head, size_t count);
RTS_PRIVATE void ghc_rust_exit_stable_ptr_table(spEntry **table, spEntry **head);
RTS_PRIVATE StgWord ghc_rust_take_stable_ptr(spEntry *table, spEntry **head, StgPtr value);
RTS_PRIVATE void ghc_rust_release_stable_ptr(spEntry **head, spEntry *slot);
RTS_PRIVATE void ghc_rust_grow_stable_ptr_table(spEntry **table, spEntry **head, size_t old_count);
RTS_PRIVATE void ghc_rust_free_old_stable_ptr_tables(void);
#else
/* Each time the stable pointer table is enlarged, we temporarily retain the old
 * version to ensure dereferences are thread-safe (see Note [Enlarging the
 * stable pointer table]).  Since we double the size of the table each time, we
 * can (theoretically) enlarge it at most N times on an N-bit machine.  Thus,
 * there will never be more than N old versions of the table.
 */
#if SIZEOF_VOID_P == 4
#define MAX_N_OLD_SPTS 32
#elif SIZEOF_VOID_P == 8
#define MAX_N_OLD_SPTS 64
#else
#error unknown SIZEOF_VOID_P
#endif

// old stable pointer tables
static spEntry *old_SPTs[MAX_N_OLD_SPTS];
static uint32_t n_old_SPTs = 0;
#endif

#if defined(THREADED_RTS)
Mutex stable_ptr_mutex;
#endif

static void enlargeStablePtrTable(void);

/* -----------------------------------------------------------------------------
 * We must lock the StablePtr table during GC, to prevent simultaneous
 * calls to freeStablePtr().
 * -------------------------------------------------------------------------- */

void
stablePtrLock(void)
{
    initStablePtrTable();
    ACQUIRE_LOCK(&stable_ptr_mutex);
}

void
stablePtrUnlock(void)
{
    RELEASE_LOCK(&stable_ptr_mutex);
}

/* -----------------------------------------------------------------------------
 * Initialising the table
 * -------------------------------------------------------------------------- */

#if !defined(USE_RUST_STABLE_PTR_TABLE)
STATIC_INLINE void
initSpEntryFreeList(spEntry *table, uint32_t n)
{
  spEntry* free = NULL;
  while (n != 0) {
      spEntry *p = &table[--n];
      p->addr = (P_)free;
      free = p;
  }
  stable_ptr_free = table;
}
#endif

void
initStablePtrTable(void)
{
    // stablePtrLock calls this before taking the mutex. Growth publishes
    // the new table with a release store. See Note [Enlarging the stable pointer table].
    if (ACQUIRE_LOAD(&stable_ptr_table) != NULL) return;
    SPT_size = INIT_SPT_SIZE;
#if defined(USE_RUST_STABLE_PTR_TABLE)
    ghc_rust_init_stable_ptr_table(&stable_ptr_table, &stable_ptr_free, INIT_SPT_SIZE);
#else
    stable_ptr_table = stgMallocBytes(SPT_size * sizeof(spEntry),
                                      "initStablePtrTable");
    initSpEntryFreeList(stable_ptr_table,INIT_SPT_SIZE);
#endif

#if defined(THREADED_RTS)
    initMutex(&stable_ptr_mutex);
#endif
}

/* -----------------------------------------------------------------------------
 * Enlarging the table
 * -------------------------------------------------------------------------- */

// Must be holding stable_ptr_mutex
static void
enlargeStablePtrTable(void)
{
    ASSERT_LOCK_HELD(&stable_ptr_mutex);

    uint32_t old_SPT_size = SPT_size;

    // Check both the entry count and the allocation size before doubling.
    if (old_SPT_size > UINT32_MAX / 2 ||
        (uint64_t)old_SPT_size * 2 * sizeof(spEntry) > SIZE_MAX) {
        barf("enlargeStablePtrTable: stable pointer table size overflow");
    }
    SPT_size *= 2;
#if defined(USE_RUST_STABLE_PTR_TABLE)
    ghc_rust_grow_stable_ptr_table(&stable_ptr_table, &stable_ptr_free, old_SPT_size);
#else
    spEntry *new_stable_ptr_table;

    /* We temporarily retain the old version instead of freeing it; see Note
     * [Enlarging the stable pointer table].
     */
    new_stable_ptr_table =
        stgMallocBytes(SPT_size * sizeof(spEntry),
                       "enlargeStablePtrTable");
    memcpy(new_stable_ptr_table,
           stable_ptr_table,
           old_SPT_size * sizeof(spEntry));
    ASSERT(n_old_SPTs < MAX_N_OLD_SPTS);
    old_SPTs[n_old_SPTs++] = stable_ptr_table;

    /* When using the threaded RTS, the update of stable_ptr_table is assumed to
     * be atomic, so that another thread simultaneously dereferencing a stable
     * pointer will always read a valid address. Release ordering to ensure
     * that the new table is visible to others.
     */
    RELEASE_STORE(&stable_ptr_table, new_stable_ptr_table);

    // add the new entries to the free list
    initSpEntryFreeList(stable_ptr_table + old_SPT_size, old_SPT_size);
#endif
}

/* Note [Enlarging the stable pointer table]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * To enlarge the stable pointer table, we allocate a new table, copy the
 * existing entries, and keep the old version in the list of retired tables
 * until we free it during GC.  By not immediately freeing the old version
 * (or equivalently by not growing the table using realloc()), we ensure that
 * another thread simultaneously dereferencing a stable pointer using the old
 * version can safely access the table without causing a segfault (see Trac
 * #10296).
 *
 * Note that because the stable pointer table is doubled in size each time it is
 * enlarged, the total memory needed to store the old versions is always less
 * than that required to hold the current version.
 */


/* -----------------------------------------------------------------------------
 * Freeing entries and tables
 * -------------------------------------------------------------------------- */

static void
freeOldSPTs(void)
{
#if defined(USE_RUST_STABLE_PTR_TABLE)
    ghc_rust_free_old_stable_ptr_tables();
#else
    uint32_t i;

    for (i = 0; i < n_old_SPTs; i++) {
        stgFree(old_SPTs[i]);
    }
    n_old_SPTs = 0;
#endif
}

void
exitStablePtrTable(void)
{
#if defined(USE_RUST_STABLE_PTR_TABLE)
    ghc_rust_exit_stable_ptr_table(&stable_ptr_table, &stable_ptr_free);
    SPT_size = 0;
#else
    if (stable_ptr_table)
        stgFree(stable_ptr_table);

    stable_ptr_table = NULL;
    stable_ptr_free = NULL;
    SPT_size = 0;

    freeOldSPTs();
#endif

#if defined(THREADED_RTS)
    closeMutex(&stable_ptr_mutex);
#endif
}

STATIC_INLINE void
freeSpEntry(spEntry *sp)
{
#if defined(USE_RUST_STABLE_PTR_TABLE)
    ghc_rust_release_stable_ptr(&stable_ptr_free, sp);
#else
    RELAXED_STORE(&sp->addr, (P_)stable_ptr_free);
    stable_ptr_free = sp;
#endif
}

void
freeStablePtrUnsafe(StgStablePtr sp)
{
    ASSERT_LOCK_HELD(&stable_ptr_mutex);

    // see Note [NULL StgStablePtr]
    if (sp == NULL) {
        return;
    }

    StgWord spw = (StgWord)sp - 1;

    ASSERT(spw < SPT_size);

    freeSpEntry(&stable_ptr_table[spw]);
}

void
freeStablePtr(StgStablePtr sp)
{
    stablePtrLock();

    freeStablePtrUnsafe(sp);

    stablePtrUnlock();
}

/* -----------------------------------------------------------------------------
 * Allocating stable pointers
 * -------------------------------------------------------------------------- */

StgStablePtr
getStablePtr(StgPtr p)
{
  stablePtrLock();

  if (!stable_ptr_free)
      enlargeStablePtrTable();

#if defined(USE_RUST_STABLE_PTR_TABLE)
  StgWord sp = ghc_rust_take_stable_ptr(stable_ptr_table, &stable_ptr_free, p);
#else
  // find the index of free stable ptr
  StgWord sp = stable_ptr_free - stable_ptr_table;

  // unlink the table entry we grabbed from the free list
  stable_ptr_free = (spEntry*)(stable_ptr_free->addr);

  // release store to pair with acquire load in deRefStablePtr
  RELEASE_STORE(&stable_ptr_table[sp].addr, p);
#endif

  stablePtrUnlock();

  // see Note [NULL StgStablePtr]
  sp = sp + 1;
  return (StgStablePtr)(sp);
}

/* -----------------------------------------------------------------------------
 * Treat stable pointers as roots for the garbage collector.
 * -------------------------------------------------------------------------- */

#if defined(USE_RUST_RTS)
GHC_STATIC_ASSERT(offsetof(spEntry, addr) == 0 &&
                  sizeof(spEntry) == sizeof(StgPtr) &&
                  _Alignof(spEntry) == _Alignof(StgPtr),
                  "Rust stable pointer entry layout");
RTS_PRIVATE void ghc_rust_visit_stable_ptrs(spEntry *table, size_t count,
                                             evac_fn evac, void *user);
#endif

/* Note [Stable pointer root slots]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * A free entry holds the address of the next free entry, or NULL.
 * A live entry holds a heap pointer. Compare numerical addresses because
 * the heap object and the stable pointer table are separate allocations.
 * The collector needs the address of the live slot to update it in place.
 */
static void
visitStablePtrTable(evac_fn evac, void *user)
{
#if defined(USE_RUST_RTS)
    ghc_rust_visit_stable_ptrs(stable_ptr_table, SPT_size, evac, user);
#else
    spEntry *table = stable_ptr_table;
    const unsigned int count = SPT_size;
    const size_t bytes = (size_t)count * sizeof(*table);

    for (unsigned int i = 0; i < count; i++) {
        StgPtr addr = table[i].addr;
        if (addr != NULL && (uintptr_t)addr - (uintptr_t)table >= bytes) {
            evac(user, (StgClosure **)&table[i].addr);
        }
    }
#endif
}

void
markStablePtrTable(evac_fn evac, void *user)
{
    /* Since no other thread can currently be dereferencing a stable pointer, it
     * is safe to free the old versions of the table.
     */
    freeOldSPTs();

    visitStablePtrTable(evac, user);
}

/* -----------------------------------------------------------------------------
 * Thread the stable pointer table for compacting GC.
 *
 * Here we must call the supplied evac function for each pointer into
 * the heap from the stable tables, because the compacting
 * collector may move the object it points to.
 * -------------------------------------------------------------------------- */

void
threadStablePtrTable( evac_fn evac, void *user )
{
    visitStablePtrTable(evac, user);
}
