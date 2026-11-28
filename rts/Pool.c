/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2014-2015
 *
 * A pool of lazily allocated things
 *
 * --------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"
#include "RtsUtils.h"
#include "Pool.h"
#include <stddef.h>

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_POOL 1
#endif

#if !defined(USE_RUST_POOL)
/* used to mark an entry as needing to be freed when released */
#define FLAG_SHOULD_FREE (1 << 0)
#endif

typedef struct PoolEntry_ PoolEntry;
#if !defined(USE_RUST_POOL)
struct PoolEntry_ {
    struct PoolEntry_ *next;
    void *thing;
    StgWord flags;
};
#endif

typedef struct PoolState_ {
    /* the maximum number of allocated resources in the pool */
    uint32_t max_size;
    /* the number of allocated resources to keep in the pool when idle */
    uint32_t desired_size;
    /* how many things are currently allocated? (sum of lengths of available and
     * taken lists) */
    uint32_t current_size;
    alloc_thing_fn alloc_fn;
    free_thing_fn free_fn;
    PoolEntry *available;
    PoolEntry *taken;
} PoolState;

struct Pool_ {
    PoolState state;
#if defined(THREADED_RTS)
    /* signaled when a thing is released or capacity increases */
    Condition cond;
    /* protects entire data structure */
    Mutex mutex;
#endif
};

/* Note [Pool list ownership]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~
 * C owns the mutex, condition, and pool lifetime. Rust owns list nodes when
 * USE_RUST_POOL is set. C holds the mutex during each Rust call. Both paths
 * call resource callbacks while holding the mutex. Callers must stop using
 * the pool before poolFree closes its condition.
 */
#if defined(USE_RUST_POOL)
GHC_STATIC_ASSERT(sizeof(PoolState) == 48, "PoolState size");
GHC_STATIC_ASSERT(offsetof(PoolState, max_size) == 0, "PoolState max_size");
GHC_STATIC_ASSERT(offsetof(PoolState, desired_size) == 4, "PoolState desired_size");
GHC_STATIC_ASSERT(offsetof(PoolState, current_size) == 8, "PoolState current_size");
GHC_STATIC_ASSERT(offsetof(PoolState, alloc_fn) == 16, "PoolState alloc_fn");
GHC_STATIC_ASSERT(offsetof(PoolState, free_fn) == 24, "PoolState free_fn");
GHC_STATIC_ASSERT(offsetof(PoolState, available) == 32, "PoolState available");
GHC_STATIC_ASSERT(offsetof(PoolState, taken) == 40, "PoolState taken");
RTS_PRIVATE int ghc_rust_pool_try_take(PoolState *state, void **thing);
RTS_PRIVATE int ghc_rust_pool_release(PoolState *state, void *thing);
RTS_PRIVATE void ghc_rust_pool_trim(PoolState *state, uint32_t size);
RTS_PRIVATE void ghc_rust_pool_flush_taken(PoolState *state);
#endif

enum {
    POOL_TAKE_EXHAUSTED = 0,
    POOL_TAKE_SUCCESS = 1,
    POOL_TAKE_ALLOC_FAILED = 2
};

static void free_available(Pool *pool, uint32_t size);

Pool *poolInit(uint32_t max_size, uint32_t desired_size,
               alloc_thing_fn alloc_fn, free_thing_fn free_fn) {
    Pool *pool = stgMallocBytes(sizeof(Pool), "pool_init");
    pool->state.max_size = max_size == 0 ? (uint32_t) -1 : max_size;
    pool->state.desired_size = desired_size;
    pool->state.current_size = 0;
    pool->state.alloc_fn = alloc_fn;
    pool->state.free_fn = free_fn;
    pool->state.available = NULL;
    pool->state.taken = NULL;
#if defined(THREADED_RTS)
    initMutex(&pool->mutex);
    initCondition(&pool->cond);
#endif
    return pool;
}

int poolFree(Pool *pool) {
    ACQUIRE_LOCK(&pool->mutex);
    if (pool->state.taken != NULL) {
        RELEASE_LOCK(&pool->mutex);
        return 1;
    }

    free_available(pool, 0);
    RELEASE_LOCK(&pool->mutex);
#if defined(THREADED_RTS)
    closeCondition(&pool->cond);
    closeMutex(&pool->mutex);
#endif
    stgFree(pool);
    return 0;
}

/* free available entries such that current_size <= size */
static void free_available(Pool *pool, uint32_t size) {
#if defined(USE_RUST_POOL)
    ghc_rust_pool_trim(&pool->state, size);
#else
    while (pool->state.current_size > size && pool->state.available != NULL) {
        PoolEntry *ent = pool->state.available;
        pool->state.free_fn(ent->thing);
        pool->state.available = ent->next;
        stgFree(ent);
        pool->state.current_size--;
    }
#endif
}

void poolSetDesiredSize(Pool *pool, uint32_t size) {
    ACQUIRE_LOCK(&pool->mutex);
    RELAXED_STORE(&pool->state.desired_size, size);
    free_available(pool, size);
    RELEASE_LOCK(&pool->mutex);
}

void poolSetMaxSize(Pool *pool, uint32_t size) {
    ACQUIRE_LOCK(&pool->mutex);
    if (size == 0)
        size = (uint32_t) -1;
#if defined(THREADED_RTS)
    uint32_t old_size = pool->state.max_size;
#endif
    RELAXED_STORE(&pool->state.max_size, size);
    if (pool->state.desired_size > size) {
        RELAXED_STORE(&pool->state.desired_size, size);
        free_available(pool, size);
    }
#if defined(THREADED_RTS)
    if (size > old_size)
        broadcastCondition(&pool->cond);
#endif
    RELEASE_LOCK(&pool->mutex);
}

/* Callbacks run with the pool mutex held. They can query either limit.
 * Each query reads one value and does not publish other pool state. */
uint32_t poolGetMaxSize(Pool *pool) {
    return RELAXED_LOAD(&pool->state.max_size);
}

uint32_t poolGetDesiredSize(Pool *pool) {
    return RELAXED_LOAD(&pool->state.desired_size);
}

/* Return a POOL_TAKE status. */
static int poolTryTake_(Pool *pool, void **thing) {
#if defined(USE_RUST_POOL)
    return ghc_rust_pool_try_take(&pool->state, thing);
#else
    PoolEntry *ent = NULL;
    if (pool->state.available != NULL) {
        ent = pool->state.available;
        pool->state.available = ent->next;
    } else if (pool->state.current_size < pool->state.max_size) {
        ent = stgMallocBytes(sizeof(PoolEntry), "pool_take");
        ent->flags = 0;
        ent->thing = pool->state.alloc_fn();
        if (ent->thing == NULL) {
            stgFree(ent);
            return POOL_TAKE_ALLOC_FAILED;
        }
        pool->state.current_size++;
    } else {
        return POOL_TAKE_EXHAUSTED;
    }

    ent->next = pool->state.taken;
    pool->state.taken = ent;
    *thing = ent->thing;
    return POOL_TAKE_SUCCESS;
#endif
}

void *poolTryTake(Pool *pool) {
    ACQUIRE_LOCK(&pool->mutex);
    void *thing = NULL;
    int result = poolTryTake_(pool, &thing);
#if defined(THREADED_RTS)
    if (result == POOL_TAKE_ALLOC_FAILED)
        signalCondition(&pool->cond);
#endif
    RELEASE_LOCK(&pool->mutex);
    return result == POOL_TAKE_SUCCESS ? thing : NULL;
}

void *poolTake(Pool *pool) {
    void *thing = NULL;
    ACQUIRE_LOCK(&pool->mutex);
    for (;;) {
        int result = poolTryTake_(pool, &thing);
        if (result == POOL_TAKE_SUCCESS)
            break;
        if (result == POOL_TAKE_ALLOC_FAILED) {
#if defined(THREADED_RTS)
            signalCondition(&pool->cond);
#endif
            RELEASE_LOCK(&pool->mutex);
            return NULL;
        }
#if defined(THREADED_RTS)
        waitCondition(&pool->cond, &pool->mutex);
#else
        barf("Tried to take from an empty pool");
#endif
    }

    RELEASE_LOCK(&pool->mutex);
    return thing;
}

void poolRelease(Pool *pool, void *thing) {
    ACQUIRE_LOCK(&pool->mutex);
#if defined(USE_RUST_POOL)
    bool found = ghc_rust_pool_release(&pool->state, thing) != 0;
#else
    bool found = false;
    PoolEntry **last = &pool->state.taken;
    PoolEntry *ent = pool->state.taken;
    while (ent != NULL) {
        if (ent->thing == thing) {
            found = true;
            *last = ent->next;
            if (pool->state.current_size > pool->state.desired_size
                || ent->flags & FLAG_SHOULD_FREE) {
                pool->state.free_fn(ent->thing);
                stgFree(ent);
                pool->state.current_size--;
            } else {
                ent->next = pool->state.available;
                pool->state.available = ent;
            }
            break;
        }

        last = &ent->next;
        ent = ent->next;
    }
#endif

    if (!found)
        barf("pool_release: trying to release resource which doesn't belong to pool.");
#if defined(THREADED_RTS)
    signalCondition(&pool->cond);
#endif
    RELEASE_LOCK(&pool->mutex);
}

void poolFlush(Pool *pool) {
    ACQUIRE_LOCK(&pool->mutex);
    free_available(pool, 0);
#if defined(USE_RUST_POOL)
    ghc_rust_pool_flush_taken(&pool->state);
#else
    PoolEntry *ent = pool->state.taken;
    while (ent != NULL) {
        ent->flags |= FLAG_SHOULD_FREE;
        ent = ent->next;
    }
#endif
    RELEASE_LOCK(&pool->mutex);
}
