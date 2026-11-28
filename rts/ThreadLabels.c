/* -----------------------------------------------------------------------------
 * ThreadLabels.c
 *
 * (c) The GHC Team 2002-2003
 *
 * Table of thread labels.
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"

#include "ThreadLabels.h"
#include "RtsUtils.h"
#include "RtsFlags.h"
#include "Hash.h"
#include "Trace.h"
#include "AllocArray.h"

#include <stdlib.h>
#include <string.h>

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_THREAD_LABELS
#if defined(THREADED_RTS)
#define RUST_THREAD_LABEL_BARRIER_POSSIBLE 1
#else
#define RUST_THREAD_LABEL_BARRIER_POSSIBLE 0
#endif
RTS_PRIVATE StgArrBytes *ghc_rust_make_thread_label(Capability *cap,
                                                     const char *text,
                                                     CostCentreStack *ccs,
                                                     size_t payload_offset);
RTS_PRIVATE void ghc_rust_label_thread(StgArrBytes **slot,
                                       Capability *cap, StgTSO *tso,
                                       StgArrBytes *label, int barrier_possible);
#endif

#if !defined(USE_RUST_THREAD_LABELS)
static void
threadLabelBeforeStore(Capability *cap, StgTSO *tso,
                       StgArrBytes *old_label)
{
    if (old_label) {
        IF_NONMOVING_WRITE_BARRIER_ENABLED {
            updateRemembSetPushClosure(cap, (StgClosure *) old_label);
        }
    }
    recordClosureMutated(cap, (StgClosure *) tso);
}
#endif

/*
 * Note [Thread Labels]
 * ~~~~~~~~~~~~~~~~~~~~
 * The user may assign a textual label to a thread using the labelThread#
 * primop to help identify the thread. This label is represented by StgTSO's
 * label field which contains a pointer to a ByteArray# containing a
 * UTF-8 string.
 *
 * Note that this string isn't necessary NULL terminated; rather, its length is
 * determined by the ByteArray# length.
 */

/* Note [Thread label publication]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * A label can be read from another capability. The writer initializes its
 * ByteArray before the release store to tso->label. Cross-capability readers
 * acquire-load the pointer once and use that value to read the ByteArray.
 * The writer also acquire-loads the old pointer before the nonmoving barrier.
 * Stop-the-world collectors use the GC entry synchronization instead.
 */

void
setThreadLabel(Capability  *cap,
               StgTSO      *tso,
               char *label)
{
#if defined(USE_RUST_THREAD_LABELS)
    StgArrBytes *arr = ghc_rust_make_thread_label(cap, label, cap->r.rCCCS,
                                                  offsetof(StgArrBytes, payload));
#else
    size_t len = strlen(label);
    StgArrBytes *arr = allocateArrBytes(cap, len, cap->r.rCCCS);
#endif
    // On allocation failure don't perform the effect. It's not convenient to
    // propagate failure from here since there are multiple callers in the RTS.
    if (RTS_UNLIKELY(arr == NULL)) return;
#if !defined(USE_RUST_THREAD_LABELS)
    memcpy(&arr->payload, label, len);
#endif
    labelThread(cap, tso, arr);
}

void
labelThread(Capability  *cap,
            StgTSO      *tso,
            StgArrBytes *label)
{
#if defined(USE_RUST_THREAD_LABELS)
    ghc_rust_label_thread(&tso->label, cap, tso, label,
                          RUST_THREAD_LABEL_BARRIER_POSSIBLE);
#else
    StgArrBytes *old_label = ACQUIRE_LOAD(&tso->label);
    threadLabelBeforeStore(cap, tso, old_label);
    RELEASE_STORE(&tso->label, label);
#endif
    traceThreadLabel(cap, tso, (char *) label->payload, label->bytes);
}
