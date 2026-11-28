/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2004
 *
 * ---------------------------------------------------------------------------*/

#pragma once

#include "sm/GC.h" // for evac_fn below

#include "BeginPrivate.h"

void    initStableNameTable   ( void );
void    freeSnEntry           ( snEntry *sn );
void    exitStableNameTable   ( void );
StgClosure *makeStableName    ( Capability *cap, StgPtr p,
                                CostCentreStack *ccs );

void    rememberOldStableNameAddresses ( void );

void    threadStableNameTable ( evac_fn evac, void *user );
void    gcStableNameTable     ( void );
RTS_PRIVATE void sweepStableNameTableNonmoving ( bool (*is_alive)(StgClosure *) );
void    updateStableNameTable ( bool full );

void    stableNameLock            ( void );
void    stableNameUnlock          ( void );

extern unsigned int SNT_size;

/* Note [Stable name table visits]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Slot zero is reserved. Other slots with an address inside the table form
 * the free list. Use numerical addresses to classify distinct allocations.
 * A NULL address can occur both at the end of the free list and when a
 * pointee dies. Visit both cases so the caller can also inspect sn_obj.
 */
#define FOR_EACH_STABLE_NAME(p, CODE)                                     \
    do {                                                                  \
        snEntry *sn_table = stable_name_table;                            \
        const size_t sn_count = SNT_size;                                 \
        for (size_t sn_index = 1; sn_index < sn_count; sn_index++) {      \
            snEntry *p = &sn_table[sn_index];                             \
            if ((uintptr_t)p->addr - (uintptr_t)sn_table >=               \
                    sn_count * sizeof(*sn_table)) {                       \
                do { CODE } while (0);                                    \
            }                                                             \
        }                                                                 \
    } while (0)

#if defined(THREADED_RTS)
// needed by Schedule.c:forkProcess()
extern Mutex stable_name_mutex;
#endif

#include "EndPrivate.h"
