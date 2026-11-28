/* -----------------------------------------------------------------------------
   (c) The University of Glasgow 2001

   Arena allocation.  Arenas provide fast memory allocation at the
   expense of fine-grained recycling of storage: memory may be
   only be returned to the system by freeing the entire arena, it
   isn't possible to return individual objects within an arena.

   Do not assume that sequentially allocated objects will be adjacent
   in memory.

   Quirks: this allocator makes use of the RTS block allocator.  If
   the current block doesn't have enough room for the requested
   object, then a new block is allocated.  This means that allocating
   large objects will tend to result in wasted space at the end of
   each block.  In the worst case, half of the allocated space is
   wasted.  This allocator is therefore best suited to situations in
   which most allocations are small.
   -------------------------------------------------------------------------- */

#include "rts/PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "Arena.h"

typedef struct {
    bdescr *block;
    StgWord *start;
    StgWord *limit;
} ArenaGroup;

// Account for the blocks held by all arenas.
static StgWord arena_blocks = 0;

#if defined(USE_RUST_RTS)
RTS_PRIVATE Arena *ghc_rust_new_arena(size_t max_size);
RTS_PRIVATE void *ghc_rust_arena_alloc(Arena *arena, size_t size);
RTS_PRIVATE void ghc_rust_arena_free(Arena *arena);
RTS_PRIVATE bdescr *ghc_rust_arena_position(const Arena *arena, StgWord **cursor);
RTS_PRIVATE void ghc_rust_arena_acquire(bdescr *previous, size_t words, ArenaGroup *out);
RTS_PRIVATE bdescr *ghc_rust_arena_release(bdescr *block);
#else
struct _Arena {
    bdescr *block;
    StgWord *cursor;
    StgWord *limit;
};
#define ghc_rust_arena_acquire arenaAcquire
#define ghc_rust_arena_release arenaRelease
#endif

#if !defined(USE_RUST_RTS)
static
#endif
void ghc_rust_arena_acquire(bdescr *previous, size_t words, ArenaGroup *out)
{
    bdescr *bd;
    if (previous == NULL) {
        bd = allocBlock_lock();
    } else {
        StgWord blocks = words / BLOCK_SIZE_W + (words % BLOCK_SIZE_W != 0);
        // A zero-size request still needs a group if the current one is full.
        bd = allocGroup_lock(stg_max(blocks, 1));
        bd->gen_no  = 0;
        bd->gen     = NULL;
        bd->dest_no = 0;
        bd->flags   = 0;
        bd->free    = bd->start;
    }
    bd->link = previous;
    RELAXED_ADD(&arena_blocks, (StgWord)bd->blocks);
    *out = (ArenaGroup){bd, bd->start, bd->start + (size_t)bd->blocks * BLOCK_SIZE_W};
}

#if !defined(USE_RUST_RTS)
static
#endif
bdescr *ghc_rust_arena_release(bdescr *bd)
{
    bdescr *next = bd->link;
    StgWord blocks = RELAXED_ADD(&arena_blocks, -(StgWord)bd->blocks);
    ASSERT(blocks <= STG_WORD_MAX - bd->blocks);
    freeGroup_lock(bd);
    return next;
}

Arena *newArena(void)
{
#if defined(USE_RUST_RTS)
    return ghc_rust_new_arena(arenaMaxSize());
#else
    Arena *arena = stgMallocBytes(sizeof(Arena), "newArena");
    ArenaGroup group;
    arenaAcquire(NULL, 0, &group);
    *arena = (Arena){group.block, group.start, group.limit};
    return arena;
#endif
}

#define MIN_ALIGN 8

void *arenaAlloc(Arena *arena, size_t size)
{
#if defined(USE_RUST_RTS)
    return ghc_rust_arena_alloc(arena, size);
#else
    if (RTS_UNLIKELY(size > arenaMaxSize())) {
        exitHeapOverflow();
    }
    size = (size + MIN_ALIGN - 1) & ~(size_t)(MIN_ALIGN - 1);
    size_t words = size / sizeof(W_);

    // An exact fit starts a new group.
    if (size < (uintptr_t)arena->limit - (uintptr_t)arena->cursor) {
        void *result = arena->cursor;
        arena->cursor += words;
        return result;
    }

    ArenaGroup group;
    arenaAcquire(arena->block, words, &group);
    *arena = (Arena){group.block, group.start + words, group.limit};
    return group.start;
#endif
}

void arenaFree(Arena *arena)
{
#if defined(USE_RUST_RTS)
    ghc_rust_arena_free(arena);
#else
    bdescr *block = arena->block;
    while (block != NULL) {
        block = arenaRelease(block);
    }
    stgFree(arena);
#endif
}

StgWord arenaBlocks(void)
{
    return RELAXED_LOAD(&arena_blocks);
}

#if defined(DEBUG)
void checkPtrInArena(StgPtr p, Arena *arena)
{
    StgWord *cursor;
    bdescr *current;
#if defined(USE_RUST_RTS)
    current = ghc_rust_arena_position(arena, &cursor);
#else
    current = arena->block;
    cursor = arena->cursor;
#endif

    // Block descriptors do not track the arena cursor.
    if ((uintptr_t)p >= (uintptr_t)current->start && (uintptr_t)p < (uintptr_t)cursor) {
        return;
    }

    // Older groups can have spare space after their last allocation.
    for (bdescr *bd = current->link; bd; bd = bd->link) {
        StgPtr limit = bd->start + (size_t)bd->blocks * BLOCK_SIZE_W;
        if ((uintptr_t)p >= (uintptr_t)bd->start && (uintptr_t)p < (uintptr_t)limit) {
            return;
        }
    }

    barf("Location %p is not in arena %p", (void *)p, (void *)arena);
}
#endif
