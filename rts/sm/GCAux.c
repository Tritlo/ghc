/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 1998-2008
 *
 * Functions called from outside the GC need to be separate from GC.c,
 * because GC.c is compiled with register variable(s).
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"

#include "GC.h"
#include "CheckUnload.h"
#include "Storage.h"
#include "Compact.h"
#include "Task.h"
#include "Capability.h"
#include "Trace.h"
#include "Schedule.h"
// DO NOT include "GCTDecl.h", we don't want the register variable

/* -----------------------------------------------------------------------------
   isAlive determines whether the given closure is still alive (after
   a garbage collection) or not.  It returns the new address of the
   closure if it is alive, or NULL otherwise.

   NOTE: Use it before compaction only!
         It untags and (if needed) retags pointers to closures.
   -------------------------------------------------------------------------- */

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
GHC_STATIC_ASSERT(TAG_MASK == 7 && offsetof(StgHeader, info) == 0 &&
                  sizeof(((StgInfoTable *)0)->type) == sizeof(uint32_t), "Rust closure layout");
GHC_STATIC_ASSERT(BF_EVACUATED == 1 && BF_LARGE == 2 && BF_MARKED == 8 && BF_NONMOVING == 1024,
                  "Rust liveness block flags");
GHC_STATIC_ASSERT(IND == 27 && IND_STATIC == 28 && BLACKHOLE == 38, "Rust indirection types");
RTS_PRIVATE StgClosure *ghc_rust_is_alive(StgClosure *p, const StgWord16 *(*flags)(StgClosure *),
    bool (*marked)(StgClosure *), ptrdiff_t info_type_offset, size_t indirectee_offset);

/* Note [Block lookup for closure liveness]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * In the large address space, a megablock contains the descriptors for its
 * blocks. See Bdescr in rts/storage/Block.h. The release fast path reads the
 * flags and compaction bitmap in Rust. This avoids a C callback per closure.
 * Use the native accessors when assertions or another heap layout require them.
 */
#if defined(USE_LARGE_ADDRESS_SPACE) && !defined(ASSERTS_ENABLED) && MBLOCK_SHIFT == 20 && BLOCK_SHIFT == 12 && BDESCR_SHIFT == 6
#define RUST_LARGE_LIVENESS
GHC_STATIC_ASSERT(offsetof(bdescr, start) == 0 && offsetof(bdescr, u.bitmap) == 24 &&
                  offsetof(bdescr, flags) == 46 && offsetof(struct mblock_address_range, begin) == 0 &&
                  offsetof(struct mblock_address_range, end) == sizeof(StgWord), "Rust megablock lookup");
RTS_PRIVATE StgClosure *ghc_rust_is_alive_large(StgClosure *p, const struct mblock_address_range *range);
#endif

static const StgWord16 *livenessBlockFlags(StgClosure *q)
{
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(q));
    return HEAP_ALLOCED_GC(q) ? &Bdescr((P_)q)->flags : NULL;
}

static bool livenessMarked(StgClosure *q)
{
    return is_marked((P_)q, Bdescr((P_)q)) != 0;
}
#endif

StgClosure *
isAlive(StgClosure *p)
{
#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
    ptrdiff_t type_offset = offsetof(StgInfoTable, type);
#if defined(TABLES_NEXT_TO_CODE)
    type_offset -= (ptrdiff_t)sizeof(StgInfoTable);
#endif
#if defined(RUST_LARGE_LIVENESS)
    if (type_offset == -8 && offsetof(StgInd, indirectee) == 8) {
        return ghc_rust_is_alive_large(p, &mblock_address_space);
    }
#endif
    return ghc_rust_is_alive(p, livenessBlockFlags, livenessMarked, type_offset,
                             offsetof(StgInd, indirectee));
#else
  const StgInfoTable *info;
  bdescr *bd;
  StgWord tag;
  StgClosure *q;

  while (1) {
    /* The tag and the pointer are split, to be merged later when needed. */
    tag = GET_CLOSURE_TAG(p);
    q = UNTAG_CLOSURE(p);

    ASSERT(LOOKS_LIKE_CLOSURE_PTR(q));

    // ignore static closures
    //
    // ToDo: This means we never look through IND_STATIC, which means
    // isRetainer needs to handle the IND_STATIC case rather than
    // raising an error.
    //
    // ToDo: for static closures, check the static link field.
    // Problem here is that we sometimes don't set the link field, eg.
    // for static closures with an empty SRT or CONSTR_NOCAFs.
    //
    if (!HEAP_ALLOCED_GC(q)) {
        return p;
    }

    // ignore closures in generations that we're not collecting.
    bd = Bdescr((P_)q);

    // isAlive is used when scavenging moving generations, before the mark
    // phase. Because we don't know alive-ness of objects before the mark phase
    // we have to conservatively treat objects in the non-moving generation as
    // alive here.
    if (bd->flags & BF_NONMOVING) {
        return p;
    }

    // if it's a pointer into to-space, then we're done
    if (bd->flags & BF_EVACUATED) {
        return p;
    }

    // large objects use the evacuated flag
    if (bd->flags & BF_LARGE) {
        return NULL;
    }

    // check the mark bit for compacted generations
    if ((bd->flags & BF_MARKED) && is_marked((P_)q,bd)) {
        return p;
    }

    info = RELAXED_LOAD(&q->header.info);

    if (IS_FORWARDING_PTR(info)) {
        // alive!
        return TAG_CLOSURE(tag,(StgClosure*)UN_FORWARDING_PTR(info));
    }

    ACQUIRE_FENCE_ON(&q->header.info);
    info = INFO_PTR_TO_STRUCT(info);

    switch (info->type) {

    case IND:
    case IND_STATIC:
      // follow indirections
      p = ((StgInd *)q)->indirectee;
      continue;

    case BLACKHOLE:
        p = ((StgInd*)q)->indirectee;
        if (GET_CLOSURE_TAG(p) != 0) {
            continue;
        } else {
            return NULL;
        }

    default:
      // dead.
      return NULL;
    }
  }
#endif
}

/* -----------------------------------------------------------------------------
   Reverting CAFs
   -------------------------------------------------------------------------- */

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
GHC_STATIC_ASSERT(STATIC_BITS == 3 && STATIC_FLAG_LIST == STATIC_BITS,
                  "Rust CAF list tags");
GHC_STATIC_ASSERT(offsetof(StgIndStatic, header.info) == 0 &&
                  offsetof(StgIndStatic, static_link) == offsetof(StgIndStatic, indirectee) + sizeof(void *) &&
                  offsetof(StgIndStatic, saved_info) == offsetof(StgIndStatic, static_link) + sizeof(void *),
                  "Rust CAF layout");
RTS_PRIVATE void ghc_rust_mark_cafs(evac_fn evac, void *user, size_t payload_offset);
RTS_PRIVATE void ghc_rust_revert_cafs(size_t payload_offset);
#endif

void
revertCAFs( void )
{
#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
    ghc_rust_revert_cafs(offsetof(StgIndStatic, indirectee));
#else
    StgIndStatic *c = revertible_caf_list;

    while (c != (StgIndStatic *) END_OF_CAF_LIST) {
        c = (StgIndStatic *)UNTAG_STATIC_LIST_PTR(c);
        StgIndStatic *next = (StgIndStatic *) c->static_link;

        SET_INFO((StgClosure *)c, c->saved_info);
        c->saved_info = NULL;
        // We must reset static_link lest the major GC finds that
        // static_flag==3 and will consequently ignore references
        // into code that we are trying to unload. This would result
        // in reachable object code being unloaded prematurely.
        // See #16842.
        c->static_link = NULL;
        c = next;
    }
    revertible_caf_list = (StgIndStatic*)END_OF_CAF_LIST;
#endif
}

void
markCAFs (evac_fn evac, void *user)
{
#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
    ghc_rust_mark_cafs(evac, user, offsetof(StgIndStatic, indirectee));
#else
    /* N.B. We must both ensure that the indirectee is
     * evacuated and that we let the linker know that the CAF
     * itself is still reachable, lest it be collected (see
     * #20649).
     */
    for (StgIndStatic *c = dyn_caf_list;
         ((StgWord) c | STATIC_FLAG_LIST) != (StgWord)END_OF_CAF_LIST;
         c = (StgIndStatic *)c->static_link)
    {
        c = (StgIndStatic *)UNTAG_STATIC_LIST_PTR(c);
        evac(user, &c->indirectee);
        // See Note [Object unloading] in CheckUnload.c
        if (unload_mark_needed) markObjectCode(c);
    }

    for (StgIndStatic *c = revertible_caf_list;
         ((StgWord) c | STATIC_FLAG_LIST) != (StgWord)END_OF_CAF_LIST;
         c = (StgIndStatic *)c->static_link)
    {
        c = (StgIndStatic *)UNTAG_STATIC_LIST_PTR(c);
        evac(user, &c->indirectee);
        // See Note [Object unloading] in CheckUnload.c
        if (unload_mark_needed) markObjectCode(c);
    }
#endif
}
