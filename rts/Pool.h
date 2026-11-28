#include "Rts.h"

/*
 * Resource pools
 *
 * This module provides an implementation of a simple thread-safe resource pool.
 * A pool is a shared set of resources, the size of which is bounded by a
 * maximum size (0 indicates unbounded). Consumers can request a resource from
 * the pool with pool_take and, when finished can return it to the pool with
 * pool_release. Resources will be lazily allocated with alloc_fn as necessary.
 * If the pool is already at its maximum size when a request is made, pool_take
 * will block until a resource is released or the maximum size increases.
 *
 * The pool will free resources such that there are at most desired_size
 * resources in the pool when all resources have been released.
 *
 * The caller must keep desired_size <= max_size. poolSetDesiredSize does not
 * clamp its argument. poolSetMaxSize lowers desired_size if necessary.
 * The allocation and release callbacks can query either size limit.
 *
 */

typedef void *(*alloc_thing_fn)(void);
typedef void (*free_thing_fn)(void *);
typedef struct Pool_ Pool;

/* Create a pool of things. */
Pool *poolInit(uint32_t max_size, uint32_t desired_size,
               alloc_thing_fn alloc_fn, free_thing_fn free_fn);

/* Free a pool. Returns 0 on success or 1 if resources are claimed.
 * The caller must exclude concurrent operations before a successful free. */
int poolFree(Pool *pool);

/* Set the maximum size of a pool (0 indicates unbounded). desired_size will be
 * lowered if necessary. */
void poolSetMaxSize(Pool *pool, uint32_t size);

/* Get the maximum size of a pool */
uint32_t poolGetMaxSize(Pool *pool);

/* Set the desired size of a pool */
void poolSetDesiredSize(Pool *pool, uint32_t size);

/* Get the desired size of a pool */
uint32_t poolGetDesiredSize(Pool *pool);

/* Try to get a resource. Return NULL if the pool is full or alloc_fn fails.
 */
void *poolTryTake(Pool *pool);

/* Get a resource. Return NULL if alloc_fn fails. Wait if the pool is full in
 * a threaded runtime. Abort if the pool is full in a single-threaded runtime.
 */
void *poolTake(Pool *pool);

/* Release a thing back to the pool from which it was taken */
void poolRelease(Pool *pool, void *thing);

/* Invalidate all currently allocated resources. Things which are currently
 * taken will be freed upon release instead of being returned to the pool. */
void poolFlush(Pool *pool);
