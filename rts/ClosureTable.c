#include "rts/PosixSource.h"
#include "Rts.h"
#include "rts/prof/CCS.h"

#include "ClosureTable.h"
#include "sm/NonMovingMark.h"
#include "RtsUtils.h"
#include "AllocArray.h"

#include <string.h>

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_CLOSURE_TABLE
/* Note [Closure table Rust layout]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The table fields have the same layout in every RTS way. C checks that
 * layout against the small Rust record. Heap array headers vary by RTS way.
 * C selects fixed-layout removal only when both array offsets match.
 * C supplies the payload offset for growth and other removal layouts.
 * C supplies the slots for insertion.
 * Rust calls the RTS allocators and registers the new mutable array before
 * it publishes either array. The RTS retains the capability and heap layouts.
 */
GHC_STATIC_ASSERT(sizeof(StgWord) == sizeof(size_t),
                  "Closure table word must match Rust usize");
GHC_STATIC_ASSERT(sizeof(StgWord) == sizeof(StgClosure *),
                  "Closure table card words must match pointer slots");
GHC_STATIC_ASSERT(sizeof(enum ClosureTableMode) == sizeof(int),
                  "Closure table mode must match Rust c_int");
GHC_STATIC_ASSERT(offsetof(StgMutArrPtrs, payload) ==
                  offsetof(StgArrBytes, payload) + sizeof(StgWord),
                  "Closure table payload offsets must differ by one word");
GHC_STATIC_ASSERT(offsetof(StgMutArrPtrs, header.info) == 0,
                  "Closure table array info must be the first word");
GHC_STATIC_ASSERT(MUT_ARR_PTRS_CARD_BITS == 7 && sizeof(StgWord8) == 1,
                  "Closure table card geometry must match Rust");
GHC_STATIC_ASSERT(FREELIST_IX_USED == -2,
                  "Closure table used marker must match Rust");
GHC_STATIC_ASSERT(offsetof(ClosureTable, arr) == 0 &&
                  offsetof(ClosureTable, free) == sizeof(void *) &&
                  offsetof(ClosureTable, free_hd) == 2 * sizeof(void *) &&
                  offsetof(ClosureTable, elems) == 2 * sizeof(void *) + sizeof(int) &&
                  offsetof(ClosureTable, capacity) == 2 * sizeof(void *) + 2 * sizeof(int) &&
                  offsetof(ClosureTable, compact) == 2 * sizeof(void *) + 3 * sizeof(int) &&
                  sizeof(ClosureTable) == 2 * sizeof(void *) + 4 * sizeof(int),
                  "Closure table layout must match Rust");
RTS_PRIVATE void ghc_rust_closure_table_init(ClosureTable *t,
                                              enum ClosureTableMode mode,
                                              StgClosure *sentinel);
RTS_PRIVATE void ghc_rust_closure_table_mark(ClosureTable *t,
                                              evac_fn evac, void *user);
RTS_PRIVATE int ghc_rust_closure_table_insert(ClosureTable *t, void *v,
                                               StgClosure **slot,
                                               StgWord8 *card,
                                               const StgInfoTable **info_slot,
                                               int next_free);
#if defined(DEBUG)
RTS_PRIVATE int ghc_rust_closure_table_insert_debug(ClosureTable *t, void *v,
                                                     StgClosure **slot,
                                                     StgWord8 *card,
                                                     const StgInfoTable **info_slot,
                                                     int *free_link);
#endif
RTS_PRIVATE bool ghc_rust_closure_table_grow(
    ClosureTable *t, Capability *cap, int capacity, CostCentreStack *ccs,
    size_t slots_offset, size_t links_offset);
RTS_PRIVATE void ghc_rust_closure_table_remove_sparse(
    ClosureTable *t, Capability *barrier_cap, int ix, size_t slots_offset);
RTS_PRIVATE void ghc_rust_closure_table_remove_compact(
    ClosureTable *t, Capability *barrier_cap, int gap,
    int *ix_from, int *ix_to, size_t slots_offset);
RTS_PRIVATE void ghc_rust_closure_table_remove_sparse_native(
    ClosureTable *t, Capability *barrier_cap, int ix);
RTS_PRIVATE void ghc_rust_closure_table_remove_compact_native(
    ClosureTable *t, Capability *barrier_cap, int gap,
    int *ix_from, int *ix_to);
#define CLOSURE_TABLE_NATIVE_LAYOUT \
    (offsetof(StgMutArrPtrs, payload) == 3 * sizeof(void *) && \
     offsetof(StgArrBytes, payload) == 2 * sizeof(void *))
#if defined(THREADED_RTS)
#define CLOSURE_TABLE_BARRIER_CAP(cap) (cap)
#else
#define CLOSURE_TABLE_BARRIER_CAP(cap) NULL
#endif
#endif


void initClosureTable(ClosureTable *t, enum ClosureTableMode mode)
{
#if defined(USE_RUST_CLOSURE_TABLE)
    ghc_rust_closure_table_init(t, mode, &stg_CLOSURE_TABLE_NULL_closure);
#else
    t->arr      = (StgMutArrPtrs *) &stg_CLOSURE_TABLE_NULL_closure;
    t->free     = (StgArrBytes   *) &stg_CLOSURE_TABLE_NULL_closure;
    t->free_hd  = FREELIST_IX_NULL;
    t->capacity = 0;
    t->elems    = 0;
    t->compact  = mode;
#endif
}


void markClosureTable(evac_fn evac, void *user, ClosureTable *t)
{
#if defined(USE_RUST_CLOSURE_TABLE)
    ghc_rust_closure_table_mark(t, evac, user);
#else
    evac(user, (StgClosure **)&t->arr);
    evac(user, (StgClosure **)&t->free);
#endif
}


bool enlargeClosureTable(Capability *cap, ClosureTable *t, int newcapacity)
{
    /* Compact tables are only allowed to be enlarged when they are full.
     * Otherwise the free list would not be maintained in the right order.
     */
    ASSERT(t->compact == ClosureTableCompact ? isFullClosureTable(t) : true);

    ASSERT(newcapacity > t->capacity);

#if defined(USE_RUST_CLOSURE_TABLE)
    return ghc_rust_closure_table_grow(t, cap, newcapacity, CCS_SYSTEM_OR_NULL,
                                       offsetof(StgMutArrPtrs, payload),
                                       offsetof(StgArrBytes, payload));
#else
    StgMutArrPtrs *oldarr = t->arr;
    int oldcapacity = t->capacity;
    StgArrBytes *oldfree = t->free;

    /* Keep the free-array size and its word rounding representable. */
    if (newcapacity <= oldcapacity ||
        (StgWord)newcapacity > (HS_WORD_MAX - (sizeof(W_) - 1)) / sizeof(int))
        return false;

    StgMutArrPtrs *newarr;
    newarr = allocateMutArrPtrs(cap, newcapacity, NULL, CCS_SYSTEM_OR_NULL);
    if (RTS_UNLIKELY(newarr == NULL)) return false;

    StgArrBytes *newfree;
    StgWord arrsize = (StgWord)newcapacity * sizeof(int);
    newfree = allocateArrBytes(cap, arrsize, CCS_SYSTEM_OR_NULL);
    if (RTS_UNLIKELY(newfree == NULL)) return false;

    StgWord oldcardsize = mutArrPtrsCardTableSize(oldcapacity);
    StgWord newcardsize = mutArrPtrsCardTableSize(newcapacity);
    StgWord oldfreesizeW = ROUNDUP_BYTES_TO_WDS((StgWord)oldcapacity * sizeof(int));
    /* Copy the old elements. */
    for (int i = 0; i < oldcapacity; i++) {
        newarr->payload[i] = oldarr->payload[i];
    }
    /* Set the new elements to a null value. */
    for (int i = oldcapacity; i < newcapacity; i++) {
        newarr->payload[i] = &stg_CLOSURE_TABLE_NULL_closure;
    }
    /* Copy the the mutable array's card table. And init extra elements to 0 */
    for (StgWord i = 0; i < oldcardsize; i++) {
        newarr->payload[newcapacity+i] = oldarr->payload[oldcapacity+i];
    }
    for (StgWord i = oldcardsize; i < newcardsize; i++) {
        newarr->payload[newcapacity+i] = 0;
    }
    /* Copy the free list. */
    for (StgWord i = 0; i < oldfreesizeW; i++) {
        newfree->payload[i] = oldfree->payload[i];
    }
    /* Initialise the new free list entries.
     * They all get consed on the front of the existing free list:
     * The last new entry points to the old head entry. The new head is the
     * first of the new entries. Otherwise, point each entry to the next one.
     */
    for (int i = oldcapacity; i < newcapacity-1; i++) {
        StgArrBytesAsCInts(newfree)[i] = i+1;
    }
    StgArrBytesAsCInts(newfree)[newcapacity-1] = t->free_hd;

    /* The new array is dirty. Record it before publishing the table. */
    recordClosureMutated(cap, (StgClosure*)newarr);
    t->arr = newarr;
    t->free_hd = oldcapacity;
    t->free = newfree;
    t->capacity = newcapacity;

    return true;
#endif
}

int insertClosureTable(Capability *cap STG_UNUSED,
                       ClosureTable *t, void *v)
{
    int ix = t->free_hd;                   /* the next free entry index */

    ASSERT(ix >= 0 && ix < t->capacity);   /* and so not FREELIST_IX_NULL */
    ASSERT(t->arr->payload[ix] == &stg_CLOSURE_TABLE_NULL_closure);

    /* Note that unlike writeArray# we do not need any memory barrier here
     * because the ClosureTable is not shared between capabilities.
     *
     * Also unlike writeArray#, we don't need to use updateRemembSetPushClosure
     * for the old array entry we are overwriting, because we know that old
     * entry is stg_CLOSURE_TABLE_NULL_closure, which is static.
     */

    /* Fill in the entry with the supplied closure. */
#if defined(USE_RUST_CLOSURE_TABLE)
#if defined(DEBUG)
    int inserted = ghc_rust_closure_table_insert_debug(
        t, v, &t->arr->payload[ix],
        mutArrPtrsCard(t->arr, ix >> MUT_ARR_PTRS_CARD_BITS),
        &t->arr->header.info, &StgArrBytesAsCInts(t->free)[ix]);
#else
    int next_free = StgArrBytesAsCInts(t->free)[ix];
    int inserted = ghc_rust_closure_table_insert(
        t, v, &t->arr->payload[ix],
        mutArrPtrsCard(t->arr, ix >> MUT_ARR_PTRS_CARD_BITS),
        &t->arr->header.info, next_free);
#endif
    return inserted;
#else
    t->arr->payload[ix] = v;

    /* Mark the corresponding card table entry. */
    *mutArrPtrsCard(t->arr, ix >> MUT_ARR_PTRS_CARD_BITS) = (StgWord8)1;

    /* Mark the array as dirty. It is already on the mutated list. */
    SET_INFO((StgClosure *)t->arr, &stg_MUT_ARR_PTRS_DIRTY_info);

    /* Pop the free list */
    t->free_hd = StgArrBytesAsCInts(t->free)[ix];

    t->elems++;

    /* in debug, mark as used */
    DEBUG_ONLY(StgArrBytesAsCInts(t->free)[ix] = FREELIST_IX_USED);

    return ix;
#endif
}


void removeClosureTable(Capability *cap STG_UNUSED, ClosureTable *t, int ix)
{
    /* removeClosureTable can only be used for non-compact tables */
    ASSERT(t->compact == ClosureTableNonCompact);

    ASSERT(ix >= 0 && ix < t->capacity);

    /* in debug, was marked as used */
    ASSERT(StgArrBytesAsCInts(t->free)[ix] == FREELIST_IX_USED);

    /* Note [Closure table removal barrier in Rust]
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * The threaded C macro reads nonmoving_write_barrier_enabled as an
     * ordinary word. Rust uses a relaxed atomic read when C passes a
     * capability. The non-threaded C wrapper passes NULL, so Rust does not
     * read the flag or call the barrier. The collector enables the flag
     * during stop-the-world preparation, before mutators resume. It clears
     * the flag after marking. Rust
     * uses the C flag protocol and calls the native barrier before overwrite.
     */

    /* Normally when modifying an array element we would need to mark the card
     * table entry, if the whole array wasn't already marked as dirty then we
     * would need to mark it as so and push it onto the mutated list (as we do
     * in insertClosureTable above).
     *
     * We normally need to do those things to maintain the generational
     * invariant because we (potentially, and indeed quite likely) have an
     * object in the old GC generation (the array) pointing to an object in a
     * newer GC generation (the array element).
     *
     * Here we are overwriting with stg_CLOSURE_TABLE_NULL_closure which is
     * statically allocated and has no outgoing pointers, so cannot point into
     * a newer GC generation. So due to that, we can skip some of the normal
     * steps.
     *
     * We do however still need to do the normal work to maintain the nonmoving
     * collector's snapshot invariant. Since we're potentially about to forget
     * the old element, we need to add it to the remembered set.
     */
#if defined(USE_RUST_CLOSURE_TABLE)
    if (CLOSURE_TABLE_NATIVE_LAYOUT) {
        ghc_rust_closure_table_remove_sparse_native(
            t, CLOSURE_TABLE_BARRIER_CAP(cap), ix);
    } else {
        ghc_rust_closure_table_remove_sparse(
            t, CLOSURE_TABLE_BARRIER_CAP(cap), ix,
            offsetof(StgMutArrPtrs, payload));
    }
#else
    IF_NONMOVING_WRITE_BARRIER_ENABLED {
        updateRemembSetPushClosure(cap, t->arr->payload[ix]);
    }
    t->arr->payload[ix] = &stg_CLOSURE_TABLE_NULL_closure;

    /* push ix onto the free list */
    StgArrBytesAsCInts(t->free)[ix] = t->free_hd;
    t->free_hd = ix;

    t->elems--;
#endif
}


#if defined(__clang__)
/* Don't error on unfixable clang warnings about 'unneeded' functions used only
 * in assertsions. They may be 'unneeded' but they are still used and cannot be
 * removed (or defined conditionally). */
#pragma clang diagnostic warning "-Wunneeded-internal-declaration"
#endif

static bool isCompactClosureTable(ClosureTable *t);


void removeCompactClosureTable(Capability *cap STG_UNUSED, ClosureTable *t,
                               int ix, int *ix_from, int *ix_to)
{
    /* removeCompactClosureTable can only be used for compact tables */
    ASSERT(t->compact == ClosureTableCompact);

    ASSERT(ix >= 0 && ix < t->capacity);

    /* in debug, was marked as used */
    ASSERT(StgArrBytesAsCInts(t->free)[ix] == FREELIST_IX_USED);

    /* this action can only be used for compact tables */
    ASSERT(isCompactClosureTable(t));

#if defined(USE_RUST_CLOSURE_TABLE)
    ASSERT(t->arr->ptrs == (StgWord)t->capacity);
    if (CLOSURE_TABLE_NATIVE_LAYOUT) {
        ghc_rust_closure_table_remove_compact_native(
            t, CLOSURE_TABLE_BARRIER_CAP(cap), ix, ix_from, ix_to);
    } else {
        ghc_rust_closure_table_remove_compact(
            t, CLOSURE_TABLE_BARRIER_CAP(cap), ix, ix_from, ix_to,
            offsetof(StgMutArrPtrs, payload));
    }
#else
    int gap_ix = ix;
    int end_ix = t->elems - 1;

    /* We will move the closure item in the table to the position
     * previously inhabited by the removed closure.
     */
    *ix_from = end_ix;
    *ix_to   = gap_ix;

    /* Note that all of the steps below still need to make sense when
     * gap_ix == end_ix, though it's ok to do some unnecessary steps.
     */

    /* We're deleting the element at gap_ix */
    IF_NONMOVING_WRITE_BARRIER_ENABLED {
        updateRemembSetPushClosure(cap, t->arr->payload[gap_ix]);
    }

    /* move the end entry over the gap and mark the end as empty */
    t->arr->payload[gap_ix] = t->arr->payload[end_ix];
    t->arr->payload[end_ix] = &stg_CLOSURE_TABLE_NULL_closure;

    /* Mark the card table entry of the gap_ix that got overwritten.
     * We don't need to mark the array as dirty overall, its dirty
     * status is unchanged either way, since the set of objects it
     * points to does not change.
     *
     * See also the notes in removeClosureTable about why we can skip
     * other steps.
     */
    *mutArrPtrsCard(t->arr, gap_ix >> MUT_ARR_PTRS_CARD_BITS) = 1;

    /* push end_ix onto the free list */
    StgArrBytesAsCInts(t->free)[end_ix] = t->free_hd;
    t->free_hd = end_ix;

    t->elems--;
#endif

    ASSERT(isCompactClosureTable(t));
    ASSERT(t->arr->payload[*ix_from] == &stg_CLOSURE_TABLE_NULL_closure);
    ASSERT(*ix_from != *ix_to
         ? t->arr->payload[*ix_to] != &stg_CLOSURE_TABLE_NULL_closure
         : true);
}


/* Check compactness: all the elements should be in the positions [0..elems-1].
 * The remaining indexes [elems..capacity-1] should be empty with the free-list
 * in order.
 *
 * This is only used in DEBUG mode for ASSERTions.
 */
static bool isCompactClosureTable(ClosureTable *t)
{
    bool isCompact = true;
    for (int n = 0; n < t->elems; n++) {
        isCompact &= (t->arr->payload[n] != &stg_CLOSURE_TABLE_NULL_closure);
        isCompact &= (StgArrBytesAsCInts(t->free)[n] == FREELIST_IX_USED);
    }
    for (int n = t->elems; n < t->capacity; n++) {
        isCompact &= (t->arr->payload[n] == &stg_CLOSURE_TABLE_NULL_closure);
        /* the last element will be FREELIST_IX_NULL, otherwise it points to
           the next */
        isCompact &= (StgArrBytesAsCInts(t->free)[n] ==
                      (n == t->capacity - 1 ? FREELIST_IX_NULL : n+1));
    }
    return isCompact;
}
