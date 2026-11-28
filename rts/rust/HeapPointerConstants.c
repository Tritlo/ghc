#include "ClosureLayout.h"
#include "Capability.h"

/* See Note [Closure size build constants] in ClosureSizeConstants.c. */
FIELD(INFO_TYPE, StgInfoTable, type, uint32_t);
FIELD(INFO_PTRS, StgInfoTable, layout.payload.ptrs, uint32_t);
FIELD(CLOSURE_INFO, StgClosure, header.info, const StgInfoTable *);
FIELD(FUN_TYPE, StgFunInfoTable, f.fun_type, uint32_t);
GHC_STATIC_ASSERT(sizeof(StgHalfWord) == sizeof(uint32_t),
                  "Rust reads a 32-bit function type");
FIELD(FUN_BITMAP, StgFunInfoTable, f.b.bitmap, StgWord);
FIELD(BCO_BITMAP, StgBCO, bitmap[0], StgWord);
FIELD(LARGE_BITMAP_BITS, StgLargeBitmap, bitmap[0], StgWord);
OFFSET(BITMAP_SHIFT, BITMAP_BITS_SHIFT);
OFFSET(CLOSURE_TAG_MASK, TAG_MASK);
OFFSET(ARG_GEN_KIND, ARG_GEN);
OFFSET(ARG_GEN_BIG_KIND, ARG_GEN_BIG);
OFFSET(ARG_BCO_KIND, ARG_BCO);
OFFSET(ARG_BITMAP_TABLE_LEN, ARG_PPPPPPPP + 1);
#if defined(TABLES_NEXT_TO_CODE)
OFFSET(FUN_INFO_BIAS, sizeof(StgFunInfoTable));
GHC_STATIC_ASSERT(sizeof(((StgFunInfoTable *)0)->f.b.bitmap_offset) == sizeof(int32_t),
                  "Rust reads a signed 32-bit bitmap offset");
#else
OFFSET(FUN_INFO_BIAS, 0);
#endif
FIELD(PAYLOAD, StgClosure, payload[0], StgClosure *);
FIELD(THUNK_PAYLOAD, StgThunk, payload[0], StgClosure *);
FIELD(SELECTEE, StgSelector, selectee, StgClosure *);
FIELD(AP_FUN, StgAP, fun, StgClosure *);
FIELD(AP_ARGS, StgAP, n_args, uint32_t);
FIELD(AP_PAYLOAD, StgAP, payload[0], StgClosure *);
FIELD(PAP_FUN, StgPAP, fun, StgClosure *);
FIELD(PAP_ARGS, StgPAP, n_args, uint32_t);
FIELD(PAP_PAYLOAD, StgPAP, payload[0], StgClosure *);
FIELD(AP_STACK_FUN, StgAP_STACK, fun, StgClosure *);
FIELD(BCO_INSTRS, StgBCO, instrs, StgClosure *);
FIELD(BCO_LITERALS, StgBCO, literals, StgClosure *);
FIELD(BCO_PTRS, StgBCO, ptrs, StgClosure *);
FIELD(INDIRECTEE, StgInd, indirectee, StgClosure *);
FIELD(ARRAY_PTRS, StgMutArrPtrs, ptrs, size_t);
FIELD(ARRAY_INFO, StgMutArrPtrs, header.info, const StgInfoTable *);
FIELD(ARRAY_PAYLOAD, StgMutArrPtrs, payload[0], StgClosure *);
FIELD(CAPABILITY_CCCS, Capability, r.rCCCS, CostCentreStack *);
FIELD(SMALL_PTRS, StgSmallMutArrPtrs, ptrs, size_t);
FIELD(SMALL_PAYLOAD, StgSmallMutArrPtrs, payload[0], StgClosure *);
FIELD(MUT_VAR, StgMutVar, var, StgClosure *);
FIELD(TVAR_CURRENT, StgTVar, current_value, StgClosure *);
FIELD(TVAR_FIRST_WATCH, StgTVar, first_watch_queue_entry, StgTVarWatchQueue *);
FIELD(MUTLIST_BD_GEN, bdescr, gen, struct generation_ *);
FIELD(MUTLIST_BD_LINK, bdescr, link, bdescr *);
FIELD(MUTLIST_BD_START, bdescr, start, StgPtr);
FIELD(MUTLIST_BD_FREE, bdescr, free, StgPtr);
#if defined(TABLES_NEXT_TO_CODE)
OFFSET(MUTLIST_INFO_BIAS, sizeof(StgInfoTable));
#else
OFFSET(MUTLIST_INFO_BIAS, 0);
#endif
OFFSET(MUTLIST_MBLOCK_SHIFT, MBLOCK_SHIFT);
OFFSET(MUTLIST_BLOCK_SHIFT, BLOCK_SHIFT);
OFFSET(MUTLIST_BDESCR_SHIFT, BDESCR_SHIFT);
OFFSET(MUTLIST_BLOCK_SIZE_W, BLOCK_SIZE_W);
#if defined(ASSERTS_ENABLED)
OFFSET(MUTLIST_ASSERTS, 1);
#else
OFFSET(MUTLIST_ASSERTS, 0);
#endif
#if defined(USE_LARGE_ADDRESS_SPACE) && !defined(ASSERTS_ENABLED)
OFFSET(MUTLIST_INLINE_CLEAN, 1);
#else
OFFSET(MUTLIST_INLINE_CLEAN, 0);
#endif
FIELD(MVAR_HEAD, StgMVar, head, StgClosure *);
FIELD(MVAR_TAIL, StgMVar, tail, StgClosure *);
FIELD(MVAR_VALUE, StgMVar, value, StgClosure *);
FIELD(TSO_LINK, StgTSO, _link, StgClosure *);
FIELD(TSO_GLOBAL, StgTSO, global_link, StgClosure *);
FIELD(TSO_STACK, StgTSO, stackobj, StgClosure *);
FIELD(TSO_TREC, StgTSO, trec, StgClosure *);
FIELD(TSO_EXCEPTIONS, StgTSO, blocked_exceptions, StgClosure *);
FIELD(TSO_BQ, StgTSO, bq, StgClosure *);
FIELD(TSO_LABEL, StgTSO, label, StgClosure *);
FIELD(WEAK_CFINALIZERS, StgWeak, cfinalizers, StgClosure *);
FIELD(WEAK_KEY, StgWeak, key, StgClosure *);
FIELD(WEAK_VALUE, StgWeak, value, StgClosure *);
FIELD(WEAK_FINALIZER, StgWeak, finalizer, StgClosure *);
FIELD(WEAK_LINK, StgWeak, link, StgClosure *);
FIELD(BQ_LINK, StgBlockingQueue, link, StgClosure *);
FIELD(BQ_BH, StgBlockingQueue, bh, StgClosure *);
FIELD(BQ_OWNER, StgBlockingQueue, owner, StgClosure *);
FIELD(BQ_QUEUE, StgBlockingQueue, queue, StgClosure *);

TAG(INVALID_OBJECT); TAG(ARR_WORDS); TAG(STACK);
TAG(CONSTR_1_0); TAG(CONSTR_0_1); TAG(CONSTR_2_0);
TAG(CONSTR_1_1); TAG(CONSTR_0_2); TAG(CONSTR);
TAG(CONSTR_NOCAF); TAG(PRIM); TAG(FUN);
TAG(FUN_0_1); TAG(FUN_1_0); TAG(FUN_1_1);
TAG(FUN_2_0); TAG(FUN_0_2); TAG(FUN_STATIC);
TAG(THUNK); TAG(THUNK_1_0); TAG(THUNK_0_1);
TAG(THUNK_1_1); TAG(THUNK_2_0); TAG(THUNK_0_2);
TAG(THUNK_STATIC); TAG(THUNK_SELECTOR); TAG(AP);
TAG(PAP); TAG(AP_STACK); TAG(BCO);
TAG(IND); TAG(IND_STATIC); TAG(BLACKHOLE);
TAG(MUT_ARR_PTRS_CLEAN); TAG(MUT_ARR_PTRS_DIRTY); TAG(MUT_ARR_PTRS_FROZEN_CLEAN);
TAG(MUT_ARR_PTRS_FROZEN_DIRTY); TAG(SMALL_MUT_ARR_PTRS_CLEAN); TAG(SMALL_MUT_ARR_PTRS_DIRTY);
TAG(SMALL_MUT_ARR_PTRS_FROZEN_CLEAN); TAG(SMALL_MUT_ARR_PTRS_FROZEN_DIRTY); TAG(MUT_VAR_CLEAN);
TAG(MUT_VAR_DIRTY); TAG(MVAR_DIRTY); TAG(MVAR_CLEAN);
TAG(TSO); TAG(WEAK); TAG(CONTINUATION);
TAG(TVAR);
TAG(BLOCKING_QUEUE);

#if defined(ASSERTS_ENABLED)
const char ghc_rust_u32_CHECK_TSO[2] = {0};
#else
const char ghc_rust_u32_CHECK_TSO[1] = {0};
#endif
