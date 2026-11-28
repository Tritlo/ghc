#include "Rts.h"
#include "Arena.h"

#include <assert.h>
#include <string.h>

static void check_arena_bound(void)
{
    const uint64_t capacity = arenaMaxSize();
    const uint64_t blocks = capacity / BLOCK_SIZE;
    const uint64_t group = BLOCKS_TO_MBLOCKS(blocks);

    assert(capacity % BLOCK_SIZE == 0);
    assert(group * MBLOCK_SIZE <= SIZE_MAX);
    assert(blocks == MBLOCK_GROUP_BLOCKS(group));
    assert(blocks <= UINT32_MAX);

    // Exercise the next group using wider arithmetic without allocating it.
    assert((group + 1) * MBLOCK_SIZE > SIZE_MAX ||
           blocks + MBLOCK_SIZE / BLOCK_SIZE > UINT32_MAX);
}

int main(int argc, char **argv)
{
    check_arena_bound();
    hs_init(&argc, &argv);

    Arena *arena = newArena();
    void *zero = arenaAlloc(arena, 0);
    unsigned char *small = arenaAlloc(arena, 1);
    assert(zero == small);
    assert((uintptr_t)small % 8 == 0);
    *small = 123;

    // An exact fit in the current group starts a new group.
    unsigned char *exact = arenaAlloc(arena, BLOCK_SIZE - 8);
    assert(exact != small + 8);
    memset(exact, 71, BLOCK_SIZE - 8);

    unsigned char *large = arenaAlloc(arena, 2 * BLOCK_SIZE + 1);
    large[2 * BLOCK_SIZE] = 5;
    assert(*small == 123);
    assert(exact[BLOCK_SIZE - 9] == 71);
    assert(large[2 * BLOCK_SIZE] == 5);

    arenaFree(arena);

    // A full group must leave a valid cursor for the next zero-size request.
    arena = newArena();
    unsigned char *full = arenaAlloc(arena, BLOCK_SIZE);
    full[BLOCK_SIZE - 1] = 42;
    zero = arenaAlloc(arena, 0);
    small = arenaAlloc(arena, 1);
    assert(zero == small);
    assert((uintptr_t)small % 8 == 0);
    *small = 71;
    assert(full[BLOCK_SIZE - 1] == 42);
    arenaFree(arena);
    hs_exit();
    return 0;
}
