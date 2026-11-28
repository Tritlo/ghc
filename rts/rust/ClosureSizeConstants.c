#include "ClosureLayout.h"
#include "Capability.h"
#include "sm/NonMovingCensus.h"

/* Note [Closure size build constants]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Hadrian compiles this file with the headers and flags of the selected RTS way.
 * For example, profiling changes the header size, and the threaded way changes
 * the size of StgTRecChunk. As in deriveConstants, each symbol has one byte
 * more than its value so nm can also report constants whose value is zero.
 * Hadrian reads the symbol sizes to generate Rust constants. Only the Rust
 * implementation goes into the RTS library.
 */
#define WORDS(name, type) const char ghc_rust_u32_##name[1 + sizeofW(type)] = {0}

FIELD(CLOSURE_INFO_OFFSET, StgClosure, header.info, const StgInfoTable *);
FIELD(CAF_SAVED_INFO, StgIndStatic, saved_info, const StgInfoTable *);
#if defined(TABLES_NEXT_TO_CODE)
OFFSET(INFO_TABLE_BIAS, sizeof(StgInfoTable));
#else
OFFSET(INFO_TABLE_BIAS, 0);
#endif
FIELD(NM_FILLED, struct NonmovingAllocator, filled, struct NonmovingSegment *);
FIELD(NM_ACTIVE, struct NonmovingAllocator, active, struct NonmovingSegment *);
FIELD(NM_BLOCK_SIZE, struct NonmovingAllocator, block_size, uint16_t);
FIELD(NM_BLOCK_COUNT, struct NonmovingAllocator, block_count, uint16_t);
OFFSET(NM_STRUCT_SIZE, sizeof(struct NonmovingAllocator));
FIELD(SEG_LINK, struct NonmovingSegment, link, struct NonmovingSegment *);
FIELD(SEG_BITMAP, struct NonmovingSegment, bitmap[0], uint8_t);
OFFSET(NM_SEGMENT_BITS, NONMOVING_SEGMENT_BITS);
FIELD(SEG_NEXT_FREE, struct NonmovingSegment, next_free, uint16_t);
FIELD(BD_NEXT_FREE_SNAP, bdescr, nonmoving_segment.next_free_snap, uint16_t);
FIELD(BD_ALLOCATOR_IDX, bdescr, nonmoving_segment.allocator_idx, uint16_t);
FIELD(BD_SCAN, bdescr, u.scan, StgPtr);
FIELD(BD_LINK, bdescr, link, bdescr *);
FIELD(BD_START, bdescr, start, StgPtr);
FIELD(COMPACT_BLOCK_OWNER, StgCompactNFDataBlock, owner, StgCompactNFData *);
FIELD(COMPACT_BLOCK_NEXT, StgCompactNFDataBlock, next, StgCompactNFDataBlock *);
OFFSET(SEG_STRUCT_SIZE, sizeof(struct NonmovingSegment));
FIELD(CAP_CURRENT_SEGMENTS, Capability, current_segments, struct NonmovingSegment **);
FIELD(CENSUS_COLLECTED, struct NonmovingAllocCensus, collected_live_words, bool);
FIELD(CENSUS_ACTIVE, struct NonmovingAllocCensus, n_active_segs, uint32_t);
FIELD(CENSUS_FILLED, struct NonmovingAllocCensus, n_filled_segs, uint32_t);
FIELD(CENSUS_BLOCKS, struct NonmovingAllocCensus, n_live_blocks, uint32_t);
FIELD(CENSUS_WORDS, struct NonmovingAllocCensus, n_live_words, uint32_t);
OFFSET(CENSUS_SIZE, sizeof(struct NonmovingAllocCensus));
FIELD(INFO_TYPE_OFFSET, StgInfoTable, type, uint32_t);
FIELD(INFO_PTRS_OFFSET, StgInfoTable, layout.payload.ptrs, uint32_t);
FIELD(INFO_NPTRS_OFFSET, StgInfoTable, layout.payload.nptrs, uint32_t);
FIELD(PAP_N_ARGS_OFFSET, StgPAP, n_args, uint32_t);
FIELD(AP_N_ARGS_OFFSET, StgAP, n_args, uint32_t);
FIELD(AP_STACK_SIZE_OFFSET, StgAP_STACK, size, size_t);
FIELD(ARR_BYTES_OFFSET, StgArrBytes, bytes, size_t);
FIELD(MUT_ARR_SIZE_OFFSET, StgMutArrPtrs, size, size_t);
FIELD(SMALL_ARR_PTRS_OFFSET, StgSmallMutArrPtrs, ptrs, size_t);
FIELD(STACK_SIZE_OFFSET, StgStack, stack_size, uint32_t);
FIELD(BCO_SIZE_OFFSET, StgBCO, size, uint32_t);
FIELD(CONTINUATION_SIZE_OFFSET, StgContinuation, stack_size, size_t);

WORDS(CLOSURE_WORDS, StgClosure);
WORDS(HEADER_WORDS, StgHeader);
WORDS(THUNK_WORDS, StgThunk);
WORDS(SELECTOR_WORDS, StgSelector);
WORDS(PAP_WORDS, StgPAP);
WORDS(AP_WORDS, StgAP);
WORDS(AP_STACK_WORDS, StgAP_STACK);
WORDS(IND_WORDS, StgInd);
WORDS(ARR_WORDS, StgArrBytes);
WORDS(MUT_ARR_WORDS, StgMutArrPtrs);
WORDS(SMALL_ARR_WORDS, StgSmallMutArrPtrs);
WORDS(TSO_WORDS, StgTSO);
WORDS(STACK_WORDS, StgStack);
WORDS(TREC_CHUNK_WORDS, StgTRecChunk);
WORDS(CONTINUATION_WORDS, StgContinuation);

TAG(THUNK_0_1); TAG(THUNK_1_0);
TAG(FUN_0_1); TAG(CONSTR_0_1); TAG(FUN_1_0); TAG(CONSTR_1_0);
TAG(THUNK_0_2); TAG(THUNK_1_1); TAG(THUNK_2_0);
TAG(FUN_0_2); TAG(CONSTR_0_2); TAG(FUN_1_1); TAG(CONSTR_1_1);
TAG(FUN_2_0); TAG(CONSTR_2_0);
TAG(THUNK); TAG(THUNK_SELECTOR); TAG(AP_STACK); TAG(AP); TAG(PAP); TAG(IND);
TAG(ARR_WORDS); TAG(MUT_ARR_PTRS_CLEAN); TAG(MUT_ARR_PTRS_DIRTY);
TAG(MUT_ARR_PTRS_FROZEN_CLEAN); TAG(MUT_ARR_PTRS_FROZEN_DIRTY);
TAG(SMALL_MUT_ARR_PTRS_CLEAN); TAG(SMALL_MUT_ARR_PTRS_DIRTY);
TAG(SMALL_MUT_ARR_PTRS_FROZEN_CLEAN); TAG(SMALL_MUT_ARR_PTRS_FROZEN_DIRTY);
TAG(TSO); TAG(STACK); TAG(BCO); TAG(TREC_CHUNK); TAG(CONTINUATION);
