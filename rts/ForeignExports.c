/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 2020
 *
 * Management of foreign exports.
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "RtsUtils.h"
#include "ForeignExports.h"
#include <stddef.h>

#if defined(USE_RUST_RTS) && defined(__x86_64__) && defined(__linux__) && !defined(TSAN_ENABLED)
#define USE_RUST_FOREIGN_EXPORTS 1
GHC_STATIC_ASSERT(sizeof(struct ForeignExportsList) == 32, "ForeignExportsList size");
GHC_STATIC_ASSERT(offsetof(struct ForeignExportsList, next) == 0, "ForeignExportsList next");
GHC_STATIC_ASSERT(offsetof(struct ForeignExportsList, n_entries) == 8, "ForeignExportsList n_entries");
GHC_STATIC_ASSERT(offsetof(struct ForeignExportsList, oc) == 16, "ForeignExportsList oc");
GHC_STATIC_ASSERT(offsetof(struct ForeignExportsList, stable_ptrs) == 24, "ForeignExportsList stable_ptrs");
GHC_STATIC_ASSERT(offsetof(struct ForeignExportsList, exports) == 32, "ForeignExportsList exports");
RTS_PRIVATE void ghc_rust_foreign_exports_enqueue(struct ForeignExportsList *exports);
RTS_PRIVATE bool ghc_rust_foreign_exports_is_loading(void);
RTS_PRIVATE void ghc_rust_foreign_exports_begin_loading(ObjectCode *oc);
RTS_PRIVATE void ghc_rust_foreign_exports_finish_loading(
    void (*check)(struct ForeignExportsList *),
    struct ForeignExportsList **(*head)(ObjectCode *));
RTS_PRIVATE void ghc_rust_foreign_exports_process(
    void (*check)(struct ForeignExportsList *),
    struct ForeignExportsList **(*head)(ObjectCode *));

/* Keep the private ObjectCode layout in C. */
static struct ForeignExportsList **foreignExportsHead(ObjectCode *oc)
{
    return &oc->foreign_exports;
}

#if defined(DEBUG)
static void assertUnprocessedForeignExports(struct ForeignExportsList *exports)
{
    ASSERT(exports->stable_ptrs == NULL);
}
#define RUST_EXPORTS_CHECK assertUnprocessedForeignExports
#else
#define RUST_EXPORTS_CHECK NULL
#endif
#endif

/* protected by linker_mutex after start-up */
#if !defined(USE_RUST_FOREIGN_EXPORTS)
static struct ForeignExportsList *pending = NULL;
static ObjectCode *loading_obj = NULL;
#endif

/*
 * Note [Tracking foreign exports]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Foreign exports are garbage collection roots. That is, things (e.g. CAFs)
 * depended upon by a module's `foreign export`s need to be kept alive for as
 * long an module is loaded. To ensure this we create a stable pointer to each
 * `foreign export`'d closure. This works as follows:
 *
 * 1. The compiler  (namely GHC.HsToCore.Foreign.Decl.foreignExports)
 *    inserts a C-stub into each module containing a `foreign export`. This
 *    stub contains two things:
 *
 *    - A `ForeignExportsList` listing all of the exported closures, and
 *
 *    - An initializer which calls `registerForeignExports` with a reference to
 *      the `ForeignExportsList`.
 *
 * 2. When the module's object code is loaded, its initializer is called by the
 *    linker (this might be the system's dynamic linker or GHC's own static
 *    linker). `registerForeignExports` then places the module's
 *    `ForeignExportsList` on `pending` list.
 *
 * 3. When loading has finished (e.g. during RTS initialization or at the end
 *    of `Linker.c:ocTryLoad`) `processForeignExports` is called. Here we
 *    traverse the `pending` list and create a `StablePtr` for each export
 *    therein.
 *
 * The reason for this two-step process is that we are very restricted in what
 * we can do in an initializer function. For instance, we cannot necessarily
 * call `malloc`  since the `libc`'s own initializer may not have run yet.
 * For instance, doing exactly this resulted in #18548.
 *
 * Another consideration here is that the linker needs to know which
 * `StablePtr`s belong to each `ObjectCode` so it can free them when the module is
 * unloaded.  For this reason, the linker informs us when it is loading an
 * object by calling `foreignExportsLoadingObject` and
 * `foreignExportsFinishedLoadingObject`. We take note of the `ObjectCode*` we
 * are loading in `loading_obj` such that we can associate the `ForeignExportsList` with
 * the `ObjectCode` in `processForeignExports`. We then record each of the
 * StablePtrs we create in the ->stable_ptrs array of ForeignExportsList so
 * they can be enumerated during unloading.
 *
 * The mixed RTS keeps the pending head and the current owner in Rust.
 * After startup the caller holds linker_mutex. Remove each list from the
 * pending queue before creating roots. A constructor that registers another
 * list during root creation must see the updated head. Clear the current
 * owner before draining at the end of a load.
 */

void registerForeignExports(struct ForeignExportsList *exports)
{
    ASSERT(exports->next == NULL);
    ASSERT(exports->oc == NULL);
#if defined(USE_RUST_FOREIGN_EXPORTS)
    ghc_rust_foreign_exports_enqueue(exports);
#else
    exports->next = pending;
    exports->oc = loading_obj;
    pending = exports;
#endif
}

/* -----------------------------------------------------------------------------
   Create a StablePtr for a foreign export.  This is normally called by
   a C function with __attribute__((constructor)), which is generated
   by GHC and linked into the module.

   If the object code is being loaded dynamically, then we remember
   which StablePtrs were allocated by the constructors and free them
   again in unloadObj().
   -------------------------------------------------------------------------- */

void foreignExportsLoadingObject(ObjectCode *oc)
{
#if defined(USE_RUST_FOREIGN_EXPORTS)
    ASSERT(!ghc_rust_foreign_exports_is_loading());
    ghc_rust_foreign_exports_begin_loading(oc);
#else
    ASSERT(loading_obj == NULL);
    loading_obj = oc;
#endif
}

void foreignExportsFinishedLoadingObject(void)
{
#if defined(USE_RUST_FOREIGN_EXPORTS)
    ASSERT(ghc_rust_foreign_exports_is_loading());
    ghc_rust_foreign_exports_finish_loading(RUST_EXPORTS_CHECK, foreignExportsHead);
#else
    ASSERT(loading_obj != NULL);
    loading_obj = NULL;
    processForeignExports();
#endif
}

/* Caller must own linker_mutex so that we can safely modify
 * oc->stable_ptrs. */
void processForeignExports(void)
{
#if defined(USE_RUST_FOREIGN_EXPORTS)
    ghc_rust_foreign_exports_process(RUST_EXPORTS_CHECK, foreignExportsHead);
#else
    while (pending) {
        struct ForeignExportsList *cur = pending;
        pending = cur->next;

        /* sanity check */
        ASSERT(cur->stable_ptrs == NULL);

        /* N.B. We only need to populate the ->stable_ptrs
         * array if the object might later be unloaded.
         */
        if (cur->oc != NULL) {
            cur->stable_ptrs =
              stgMallocBytes(sizeof(StgStablePtr*) * cur->n_entries,
                             "foreignExportStablePtr");

            for (int i=0; i < cur->n_entries; i++) {
                StgStablePtr *sptr = getStablePtr(cur->exports[i]);

                if (cur->oc != NULL) {
                    cur->stable_ptrs[i] = sptr;
                }
            }
            cur->next = cur->oc->foreign_exports;
            cur->oc->foreign_exports = cur;
        } else {
            /* can't be unloaded, don't bother populating
             * ->stable_ptrs array. */
            for (int i=0; i < cur->n_entries; i++) {
                getStablePtr(cur->exports[i]);
            }
        }
    }
#endif
}
