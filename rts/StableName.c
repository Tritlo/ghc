/* -*- tab-width: 4 -*- */

/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2002
 *
 * Stable names
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"
#include "RtsAPI.h"

#include "Hash.h"
#include "RtsUtils.h"
#include "Trace.h"
#include "StableName.h"

#include <string.h>

snEntry *stable_name_table = NULL;
static snEntry *stable_name_free = NULL;
unsigned int SNT_size = 0;
#define INIT_SNT_SIZE 64

#if defined(THREADED_RTS)
Mutex stable_name_mutex;
#endif

static void enlargeStableNameTable(void);

/*
 * This hash table maps Haskell objects to stable names, so that every
 * call to makeStableName on a given object will return the same
 * stable name.
 */

static HashTable *addrToStableHash = NULL;

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_STABLE_NAME_TABLE 1
RTS_PRIVATE void ghc_rust_init_stable_name_table(snEntry **table,
                                                 snEntry **free,
                                                 size_t count);
RTS_PRIVATE void ghc_rust_grow_stable_name_table(snEntry **table,
                                                 snEntry **free,
                                                 size_t old_count);
RTS_PRIVATE void ghc_rust_exit_stable_name_table(snEntry **table);
RTS_PRIVATE StgWord ghc_rust_reserve_stable_name(snEntry *table,
                                                snEntry **free,
                                                HashTable *hash,
                                                StgPtr addr);
RTS_PRIVATE void ghc_rust_gc_stable_name_table(snEntry *table, size_t count,
    snEntry **free, HashTable *hash,
    StgClosure *(*is_alive)(StgClosure *),
    void (*trace_dead_name)(size_t, StgPtr),
    void (*trace_dead_pointee)(size_t));
RTS_PRIVATE void ghc_rust_sweep_stable_names(snEntry *table, size_t count,
    snEntry **free, HashTable *hash, bool (*is_alive)(StgClosure *));
RTS_PRIVATE StgClosure *ghc_rust_stable_name_key(StgClosure *p,
    ptrdiff_t info_type_offset, size_t indirectee_offset);
#endif

void
stableNameLock(void)
{
    initStableNameTable();
    ACQUIRE_LOCK(&stable_name_mutex);
}

void
stableNameUnlock(void)
{
    RELEASE_LOCK(&stable_name_mutex);
}

/* -----------------------------------------------------------------------------
 * Initialising the table
 * -------------------------------------------------------------------------- */

#if !defined(USE_RUST_STABLE_NAME_TABLE)
STATIC_INLINE void
initSnEntryFreeList(snEntry *table, uint32_t n, snEntry *free)
{
  snEntry *p;
  for (p = table + n - 1; p >= table; p--) {
    p->addr   = (P_)free;
    p->old    = NULL;
    p->sn_obj = NULL;
    free = p;
  }
  stable_name_free = table;
}
#endif

void
initStableNameTable(void)
{
    if (SNT_size > 0) return;
    SNT_size = INIT_SNT_SIZE;
#if defined(USE_RUST_STABLE_NAME_TABLE)
    ghc_rust_init_stable_name_table(&stable_name_table, &stable_name_free,
                                    INIT_SNT_SIZE);
#else
    stable_name_table = stgMallocBytes(SNT_size * sizeof(snEntry),
                                       "initStableNameTable");
    /* we don't use index 0 in the stable name table, because that
     * would conflict with the hash table lookup operations which
     * return NULL if an entry isn't found in the hash table.
     */
    initSnEntryFreeList(stable_name_table + 1,INIT_SNT_SIZE-1,NULL);
#endif
    addrToStableHash = allocHashTable();

#if defined(THREADED_RTS)
    initMutex(&stable_name_mutex);
#endif
}

/* -----------------------------------------------------------------------------
 * Enlarging the tables
 * -------------------------------------------------------------------------- */

static void
enlargeStableNameTable(void)
{
    uint32_t old_SNT_size = SNT_size;

    // Check both the entry count and the allocation size before doubling.
    if (old_SNT_size > UINT32_MAX / 2 ||
        (uint64_t)old_SNT_size * 2 * sizeof(snEntry) > SIZE_MAX) {
        barf("enlargeStableNameTable: stable name table size overflow");
    }
    SNT_size *= 2;
#if defined(USE_RUST_STABLE_NAME_TABLE)
    ghc_rust_grow_stable_name_table(&stable_name_table, &stable_name_free,
                                    old_SNT_size);
#else
    stable_name_table =
        stgReallocBytes(stable_name_table,
                        SNT_size * sizeof(snEntry),
                        "enlargeStableNameTable");

    initSnEntryFreeList(stable_name_table + old_SNT_size, old_SNT_size, NULL);
#endif
}


/* -----------------------------------------------------------------------------
 * Freeing entries and tables
 * -------------------------------------------------------------------------- */

void
exitStableNameTable(void)
{
    if (addrToStableHash)
        freeHashTable(addrToStableHash, NULL);
    addrToStableHash = NULL;

#if defined(USE_RUST_STABLE_NAME_TABLE)
    ghc_rust_exit_stable_name_table(&stable_name_table);
#else
    if (stable_name_table)
        stgFree(stable_name_table);
    stable_name_table = NULL;
#endif
    SNT_size = 0;

#if defined(THREADED_RTS)
    closeMutex(&stable_name_mutex);
#endif
}

#if defined(USE_RUST_RTS)
RTS_PRIVATE void ghc_rust_free_stable_name(snEntry *entry, snEntry **free,
                                          HashTable *hash);
#endif

void
freeSnEntry(snEntry *sn)
{
  ASSERT(sn->sn_obj == NULL);
#if defined(USE_RUST_RTS)
  ghc_rust_free_stable_name(sn, &stable_name_free, addrToStableHash);
#else
  removeHashTable(addrToStableHash, (W_)sn->old, NULL);
  sn->addr = (P_)stable_name_free;
  stable_name_free = sn;
#endif
}

/* -----------------------------------------------------------------------------
 * Looking up
 * -------------------------------------------------------------------------- */

/* Note [Stable name key]
 * ~~~~~~~~~~~~~~~~~~~~~~
 * Follow indirections before looking up a stable name. Read each indirectee
 * with acquire ordering. A BLACKHOLE with an untagged indirectee names its
 * owner: return that indirectee without examining the owner as a closure.
 * The stable name table stores the final pointer without its tag.
 */
#if defined(USE_RUST_STABLE_NAME_TABLE)
GHC_STATIC_ASSERT(TAG_MASK == 7 && offsetof(StgHeader, info) == 0 &&
                  sizeof(((StgInfoTable *)0)->type) == sizeof(uint32_t) &&
                  offsetof(StgInd, indirectee) == offsetof(StgIndStatic, indirectee) &&
                  IND == 27 && IND_STATIC == 28 && BLACKHOLE == 38,
                  "Rust stable name key closure layout");
#else
static StgClosure*
removeIndirections (StgClosure* p)
{
    StgClosure* q;

    while (1)
    {
        q = UNTAG_CLOSURE(p);

        switch (get_itbl(q)->type) {
        case IND:
        case IND_STATIC:
            p = ACQUIRE_LOAD(&((StgInd *)q)->indirectee);
            continue;

        case BLACKHOLE:
            p = ACQUIRE_LOAD(&((StgInd *)q)->indirectee);
            if (GET_CLOSURE_TAG(p) != 0) {
                continue;
            } else {
                break;
            }

        default:
            break;
        }
        return p;
    }
}
#endif

/* Note [Stable name creation]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Keep stable_name_mutex locked from the table lookup through publication of
 * sn_obj. enlargeStableNameTable can move the table. Thus, no thread can keep
 * an entry pointer or index while another thread changes the table. The lock
 * also makes one thread responsible for the StgStableName allocation.
 *
 * The caller must perform its heap check before this function. allocate does
 * not collect. This is required because the collector treats an entry with a
 * NULL sn_obj as free. See #15906. Initialize the closure and its index before
 * the release store publishes sn_obj.
 */

StgClosure *
makeStableName (Capability *cap, StgPtr p,
                CostCentreStack *ccs USED_IF_PROFILING)
{
  stableNameLock();

  if (stable_name_free == NULL) {
    enlargeStableNameTable();
  }

  /* removing indirections increases the likelihood
   * of finding a match in the stable name hash table.
   */
#if defined(USE_RUST_STABLE_NAME_TABLE)
  StgClosure *q = UNTAG_CLOSURE((StgClosure *)p);
  switch (get_itbl(q)->type) {
  case IND:
  case IND_STATIC:
  case BLACKHOLE: {
    ptrdiff_t type_offset = offsetof(StgInfoTable, type);
#if defined(TABLES_NEXT_TO_CODE)
    type_offset -= (ptrdiff_t)sizeof(StgInfoTable);
#endif
    p = (StgPtr)ghc_rust_stable_name_key((StgClosure *)p, type_offset,
        offsetof(StgInd, indirectee));
    break;
  }
  default:
    p = (StgPtr)q;
  }
#else
  p = (StgPtr)removeIndirections((StgClosure*)p);

  // register the untagged pointer.  This just makes things simpler.
  p = (StgPtr)UNTAG_CLOSURE((StgClosure*)p);
#endif

  StgWord sn = (StgWord)lookupHashTable(addrToStableHash, (W_)p);
  if (sn != 0) {
    ASSERT(stable_name_table[sn].addr == p);
    debugTrace(DEBUG_stable, "cached stable name %" FMT_Word " at %p", sn, p);
    StgClosure *sn_obj = stable_name_table[sn].sn_obj;
    if (sn_obj != NULL) {
      stableNameUnlock();
      return sn_obj;
    }
  } else {
#if defined(USE_RUST_STABLE_NAME_TABLE)
    sn = ghc_rust_reserve_stable_name(stable_name_table, &stable_name_free,
                                      addrToStableHash, p);
#else
    sn = stable_name_free - stable_name_table;
    stable_name_free  = (snEntry*)(stable_name_free->addr);
    stable_name_table[sn].addr = p;
    stable_name_table[sn].sn_obj = NULL;
    /* debugTrace(DEBUG_stable, "new stable name %d at %p\n",sn,p); */

    /* add the new stable name to the hash table */
    insertHashTable(addrToStableHash, (W_)p, (void *)sn);
#endif
  }

  // See Note [Stable name creation].
  StgStableName *sn_obj = (StgStableName *)allocate(
      cap, sizeofW(StgStableName));
  SET_HDR(sn_obj, &stg_STABLE_NAME_info, ccs);
  sn_obj->sn = sn;
  RELEASE_STORE(&stable_name_table[sn].sn_obj, (StgClosure *)sn_obj);

  stableNameUnlock();
  return (StgClosure *)sn_obj;
}

/* -----------------------------------------------------------------------------
 * Remember old stable name addresses
 * -------------------------------------------------------------------------- */

#if defined(USE_RUST_RTS)
GHC_STATIC_ASSERT(offsetof(snEntry, addr) == 0 &&
                  offsetof(snEntry, old) == sizeof(StgPtr) &&
                  offsetof(snEntry, sn_obj) == 2 * sizeof(StgPtr) &&
                  sizeof(snEntry) == 3 * sizeof(StgPtr) &&
                  _Alignof(snEntry) == _Alignof(StgPtr),
                  "Rust stable name entry layout");
RTS_PRIVATE void ghc_rust_remember_stable_names(snEntry *table, size_t count);
RTS_PRIVATE void ghc_rust_thread_stable_names(snEntry *table, size_t count,
                                              evac_fn evac, void *user);
RTS_PRIVATE void ghc_rust_update_stable_names(snEntry *table, size_t count,
                                             HashTable **hash, bool full);
#endif

void
rememberOldStableNameAddresses(void)
{
    /* TODO: Only if !full GC */
#if defined(USE_RUST_RTS)
    ghc_rust_remember_stable_names(stable_name_table, SNT_size);
#else
    FOR_EACH_STABLE_NAME(p, p->old = p->addr;);
#endif
}

/* -----------------------------------------------------------------------------
 * Thread the stable name table for compacting GC.
 *
 * Here we must call the supplied evac function for each pointer into
 * the heap from the stable name table, because the compacting
 * collector may move the object it points to.
 * -------------------------------------------------------------------------- */

void
threadStableNameTable( evac_fn evac, void *user )
{
#if defined(USE_RUST_RTS)
    ghc_rust_thread_stable_names(stable_name_table, SNT_size, evac, user);
#else
    FOR_EACH_STABLE_NAME(p, {
        if (p->sn_obj != NULL) {
            evac(user, (StgClosure **)&p->sn_obj);
        }
        if (p->addr != NULL) {
            evac(user, (StgClosure **)&p->addr);
        }
    });
#endif
}

/* -----------------------------------------------------------------------------
 * Garbage collect any dead entries in the stable name table.
 *
 * A dead entry has:
 *
 *          - a zero reference count
 *          - a dead sn_obj
 *
 * Both of these conditions must be true in order to re-use the stable
 * name table entry.  We can re-use stable name table entries for live
 * heap objects, as long as the program has no StableName objects that
 * refer to the entry.
 * -------------------------------------------------------------------------- */

/* Note [Stable name liveness pass]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * C holds the table lock during the serial pass and supplies isAlive.
 * Rust visits entries in slot order and frees dead names directly.
 * A dead name is traced before its entry joins the free list.
 */
#if defined(USE_RUST_STABLE_NAME_TABLE) && defined(DEBUG)
static void traceDeadStableName(size_t index, StgPtr addr)
{
    debugTrace(DEBUG_stable, "GC'd StableName %td (addr=%p)",
               (ptrdiff_t)index, addr);
}

static void traceDeadStablePointee(size_t index)
{
    debugTrace(DEBUG_stable, "GC'd pointee %ld", (long)index);
}
#define TRACE_DEAD_NAME traceDeadStableName
#define TRACE_DEAD_POINTEE traceDeadStablePointee
#else
#define TRACE_DEAD_NAME NULL
#define TRACE_DEAD_POINTEE NULL
#endif

void
gcStableNameTable( void )
{
    // We must take the stable name lock lest we race with the nonmoving
    // collector (namely nonmovingSweepStableNameTable).
    stableNameLock();
#if defined(USE_RUST_STABLE_NAME_TABLE)
    ghc_rust_gc_stable_name_table(stable_name_table, SNT_size,
        &stable_name_free, addrToStableHash, isAlive,
        TRACE_DEAD_NAME, TRACE_DEAD_POINTEE);
#else
    FOR_EACH_STABLE_NAME(
        p, {
            // FOR_EACH_STABLE_NAME traverses free entries too, so
            // check sn_obj
            if (p->sn_obj != NULL) {
                // Update the pointer to the StableName object, if there is one
                p->sn_obj = isAlive(p->sn_obj);
                if (p->sn_obj == NULL) {
                    // StableName object died
                    debugTrace(DEBUG_stable, "GC'd StableName %td (addr=%p)",
                               p - stable_name_table, p->addr);
                    freeSnEntry(p);
                } else if (p->addr != NULL) {
                    // sn_obj is alive, update pointee
                    p->addr = (StgPtr)isAlive((StgClosure *)p->addr);
                    if (p->addr == NULL) {
                        // Pointee died
                        debugTrace(DEBUG_stable, "GC'd pointee %ld",
                                   (long)(p - stable_name_table));
                    }
                }
            }
        });
#endif
    stableNameUnlock();
}

void
sweepStableNameTableNonmoving(bool (*is_alive)(StgClosure *))
{
    stableNameLock();
#if defined(USE_RUST_STABLE_NAME_TABLE)
    ghc_rust_sweep_stable_names(stable_name_table, SNT_size,
        &stable_name_free, addrToStableHash, is_alive);
#else
    FOR_EACH_STABLE_NAME(
        p, {
            if (p->sn_obj != NULL) {
                if (!is_alive((StgClosure *)p->sn_obj)) {
                    p->sn_obj = NULL;
                    freeSnEntry(p);
                } else if (p->addr != NULL &&
                           !is_alive((StgClosure *)p->addr)) {
                    p->addr = NULL;
                }
            }
        });
#endif
    stableNameUnlock();
}

/* -----------------------------------------------------------------------------
 * Update the StableName hash table
 *
 * The boolean argument 'full' indicates that a major collection is
 * being done, so we might as well throw away the hash table and build
 * a new one.  For a minor collection, we just re-hash the elements
 * that changed.
 * -------------------------------------------------------------------------- */

void
updateStableNameTable(bool full)
{
#if defined(USE_RUST_RTS)
    ghc_rust_update_stable_names(stable_name_table, SNT_size, &addrToStableHash, full);
#else
    if (full && addrToStableHash != NULL && 0 != keyCountHashTable(addrToStableHash)) {
        freeHashTable(addrToStableHash,NULL);
        addrToStableHash = allocHashTable();
    }

    if(full) {
        FOR_EACH_STABLE_NAME(
            p, {
                if (p->addr != NULL) {
                    // Target still alive, Re-hash this stable name
                    insertHashTable(addrToStableHash, (W_)p->addr, (void *)(p - stable_name_table));
                }
            });
    } else {
        FOR_EACH_STABLE_NAME(
            p, {
                if (p->addr != p->old) {
                    removeHashTable(addrToStableHash, (W_)p->old, NULL);
                    /* Movement happened: */
                    if (p->addr != NULL) {
                        insertHashTable(addrToStableHash, (W_)p->addr, (void *)(p - stable_name_table));
                    }
                }
            });
    }
#endif
}
