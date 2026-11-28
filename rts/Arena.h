/* -----------------------------------------------------------------------------
   (c) The University of Glasgow 2001

   Arena allocation interface.
   -------------------------------------------------------------------------- */

#pragma once

// Abstract type of arenas
typedef struct _Arena Arena;

// Start a new arena
Arena * newArena   ( void );

// Allocate memory in an arena
void  * arenaAlloc ( Arena *, size_t );

// Free an entire arena
void arenaFree  ( Arena * );

// For internal use only:
RTS_PRIVATE StgWord arenaBlocks( void );

/* The first megablock has fewer usable blocks because it holds descriptors.
 * Bound the rounded group by bdescr.blocks and the byte size sent to the OS.
 */
INLINE_HEADER size_t
arenaMaxSize(void)
{
    const size_t blocks_per_megablock = MBLOCK_SIZE / BLOCK_SIZE;
    const size_t descriptor_limit =
        1 + (UINT32_MAX - BLOCKS_PER_MBLOCK) / blocks_per_megablock;
    const size_t address_limit = SIZE_MAX / MBLOCK_SIZE;
    const size_t megablocks =
        descriptor_limit < address_limit ? descriptor_limit : address_limit;
    return MBLOCK_GROUP_BLOCKS(megablocks) * BLOCK_SIZE;
}

#if defined(DEBUG)
void checkPtrInArena( StgPtr p, Arena *arena );
#endif
