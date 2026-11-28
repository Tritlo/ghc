/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 2008 
 *
 * Simple mark/sweep, collecting whole blocks.
 *
 * Documentation on the architecture of the Garbage Collector can be
 * found in the online commentary:
 * 
 *   https://gitlab.haskell.org/ghc/ghc/wikis/commentary/rts/storage/gc
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"

#include "BlockAlloc.h"
#include "Sweep.h"
#include "Trace.h"

typedef struct {
    W_ marked, freed, fragmented, live;
} SweepStats;

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
typedef struct {
    W_ link, bitmap, flags, bitmap_words;
} SweepLayout;

RTS_PRIVATE SweepStats ghc_rust_sweep_blocks(bdescr **head, memcount *count,
                                             const SweepLayout *layout);
GHC_STATIC_ASSERT(BF_MARKED == 8 && BF_FRAGMENTED == 64 && BF_SWEPT == 256,
                  "Rust sweep flags");
GHC_STATIC_ASSERT(BLOCK_SIZE_W % BITS_IN(W_) == 0, "whole bitmap words");
#endif

void
sweep(generation *gen)
{
    ASSERT(countBlocks(gen->old_blocks) == gen->n_old_blocks);

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
    static const SweepLayout layout = {
        offsetof(bdescr, link), offsetof(bdescr, u.bitmap), offsetof(bdescr, flags),
        BLOCK_SIZE_W / BITS_IN(W_)
    };
    SweepStats stats = ghc_rust_sweep_blocks(&gen->old_blocks, &gen->n_old_blocks, &layout);
#else
    bdescr *bd, *prev, *next;
    uint32_t i;
    W_ freed, resid, fragd, blocks, live;

    live = 0; // estimate of live data in this gen
    freed = 0;
    fragd = 0;
    blocks = 0;
    prev = NULL;
    for (bd = gen->old_blocks; bd != NULL; bd = next)
    {
        next = bd->link;

        if (!(bd->flags & BF_MARKED)) { 
            prev = bd;
            continue;
        }

        blocks++;
        resid = 0;
        for (i = 0; i < BLOCK_SIZE_W / BITS_IN(W_); i++)
        {
            if (bd->u.bitmap[i] != 0) resid++;
        }
        live += resid * BITS_IN(W_);

        if (resid == 0)
        {
            freed++;
            gen->n_old_blocks--;
            if (prev == NULL) {
                gen->old_blocks = next;
            } else {
                prev->link = next;
            }
            freeGroup(bd);
        }
        else
        {
            prev = bd;
            if (resid < (BLOCK_SIZE_W * 3) / (BITS_IN(W_) * 4)) {
                fragd++;
                bd->flags |= BF_FRAGMENTED;
            }

            bd->flags |= BF_SWEPT;
        }
    }

    SweepStats stats = { blocks, freed, fragd, live };
#endif
    gen->live_estimate = stats.live;

    debugTrace(DEBUG_gc, "sweeping: %" FMT_Word " blocks, "
                                   "%" FMT_Word " were copied, "
                                   "%" FMT_Word " freed (%" FMT_Word "%%), "
                                   "%" FMT_Word " are fragmented, "
                         "live estimate: %lu%%",
          gen->n_old_blocks + stats.freed,
          gen->n_old_blocks - stats.marked + stats.freed,
          stats.freed,
          stats.marked == 0 ? 0 : (stats.freed * 100) / stats.marked,
          stats.fragmented,
          (unsigned long)((stats.marked == stats.freed) ? 0 :
              ((stats.live / BLOCK_SIZE_W) * 100) / (stats.marked - stats.freed)));

    ASSERT(countBlocks(gen->old_blocks) == gen->n_old_blocks);
}
