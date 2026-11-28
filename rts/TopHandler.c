#include "Rts.h"
#include "StablePtr.h"
#include "TopHandler.h"

/* Note [Top handler stable pointer]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The registry roots a Weak# object. Its key is the main thread.
 * The registry mutex protects stable-pointer replacement and lookup.
 * The caller holds a capability while it inspects the weak object after
 * unlocking. The collector can clear its key between calls.
 */
#if defined(THREADED_RTS)
static Mutex m;
#endif

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_TOP_HANDLER
GHC_STATIC_ASSERT(offsetof(StgWeak, header.info) == 0 &&
                  _Alignof(StgWeak) >= _Alignof(void *), "Rust weak info pointer layout");
RTS_PRIVATE void ghc_rust_top_handler_init(void);
RTS_PRIVATE void ghc_rust_top_handler_set(StgWeak *weak);
RTS_PRIVATE StgWeak *ghc_rust_top_handler_weak(void);
RTS_PRIVATE StgTSO *ghc_rust_top_handler_thread(
    StgWeak *weak, size_t key_offset, void (*check_key)(StgTSO *),
    void (*invalid_weak)(StgWeak *, const StgInfoTable *));
RTS_PRIVATE void ghc_rust_top_handler_exit(void);

#if defined(ASSERTS_ENABLED)
static void checkThreadKey(StgTSO *key)
{
    ASSERT(key && key->header.info == &stg_TSO_info);
}
#define CHECK_THREAD_KEY checkThreadKey
#else
#define CHECK_THREAD_KEY NULL
#endif
#else
static StgStablePtr topHandlerPtr;
#endif

static void invalidWeak(StgWeak *weak, const StgInfoTable *info)
{
    barf("getTopHandlerThread: neither a WEAK nor a DEAD_WEAK: %p %p %d",
         weak, info, info->type);
}

void rts_setMainThread(StgWeak *weak) {
    ACQUIRE_LOCK(&m);
#if defined(USE_RUST_TOP_HANDLER)
    ghc_rust_top_handler_set(weak);
#else
    if (topHandlerPtr != NULL) {
        freeStablePtr(topHandlerPtr); // OK to do under the lock
    }
    topHandlerPtr = getStablePtr((StgPtr)weak);
#endif
    // referent is a Weak#
    ASSERT(weak->header.info == &stg_WEAK_info);

    // See Note [rts_setMainThread has an unsound type] in
    // libraries/base/GHC/TopHandler.hs.
    ASSERT(weak->key->header.info == &stg_TSO_info);

    RELEASE_LOCK(&m);
}

StgTSO *getTopHandlerThread(void) {
    ACQUIRE_LOCK(&m);
#if defined(USE_RUST_TOP_HANDLER)
    StgWeak *weak = ghc_rust_top_handler_weak();
#else
    StgWeak *weak = (StgWeak*)deRefStablePtr(topHandlerPtr);
#endif
    RELEASE_LOCK(&m);
#if defined(USE_RUST_TOP_HANDLER)
    return ghc_rust_top_handler_thread(weak, offsetof(StgWeak, key),
                                       CHECK_THREAD_KEY, invalidWeak);
#else
    if (weak == NULL) {
        // topHandlerPtr was never initialised
        return NULL;
    }
    const StgInfoTable *info = ACQUIRE_LOAD(&weak->header.info);
    if (info == &stg_WEAK_info) {
        StgClosure *key = ((StgWeak*)weak)->key;

        // See Note [rts_setMainThread has an unsound type] in
        // libraries/base/GHC/TopHandler.hs.
        ASSERT(key->header.info == &stg_TSO_info);

        return (StgTSO *)key;
    } else if (info == &stg_DEAD_WEAK_info) {
        return NULL;
    } else {
        invalidWeak(weak, info);
        return NULL;
    }
#endif
}

void initTopHandler(void) {
#if defined(THREADED_RTS)
    initMutex(&m);
#endif
#if defined(USE_RUST_TOP_HANDLER)
    ghc_rust_top_handler_init();
#else
    topHandlerPtr = NULL;
#endif
}

void exitTopHandler(void) {
#if defined(USE_RUST_TOP_HANDLER)
    ghc_rust_top_handler_exit();
#else
    freeStablePtr(topHandlerPtr);
    topHandlerPtr = NULL;
#endif
#if defined(THREADED_RTS)
    closeMutex(&m);
#endif
}
