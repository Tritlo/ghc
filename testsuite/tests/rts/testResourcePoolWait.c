#include "Rts.h"
#include "Pool.h"
#include <errno.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdatomic.h>
#include <stdlib.h>

static sem_t waiting;
static _Thread_local bool is_waiter;
static atomic_bool fail_once;
static Pool *pool;

// When start() returns, the taker is entering its first wait with the
// pool mutex held. The next pool operation can acquire that mutex only
// after the wait has released it.
void __real_waitCondition(Condition *, Mutex *);
void __wrap_waitCondition(Condition *cond, Mutex *mutex)
{
    if (is_waiter) {
        is_waiter = false;
        if (sem_post(&waiting)) abort();
    }
    __real_waitCondition(cond, mutex);
}

static void *allocate_resource(void)
{
    if (atomic_exchange(&fail_once, false)) return NULL;
    void *p = malloc(1);
    if (!p) abort();
    return p;
}

static void *take(void *unused)
{
    (void)unused;
    is_waiter = true;
    return poolTake(pool);
}

static pthread_t start(void)
{
    pthread_t id;
    if (pthread_create(&id, NULL, take, NULL)) abort();
    int rc;
    do { rc = sem_wait(&waiting); } while (rc && errno == EINTR);
    if (rc) abort();
    return id;
}

static void *finish(pthread_t id)
{
    void *result;
    if (pthread_join(id, &result)) abort();
    return result;
}

int main(void)
{
    if (sem_init(&waiting, 0, 0)) abort();
    // A failed allocation must let the next blocked taker try.
    pool = poolInit(1, 0, allocate_resource, free);
    void *held = poolTake(pool);
    pthread_t a = start(), b = start();
    atomic_store(&fail_once, true);
    poolRelease(pool, held);
    void *x = finish(a), *y = finish(b);
    if ((x == NULL) == (y == NULL)) abort();
    poolRelease(pool, x ? x : y);
    if (poolFree(pool)) abort();

    // Raising the limit makes room for both takers without a release.
    pool = poolInit(1, 1, allocate_resource, free);
    held = poolTake(pool);
    a = start();
    b = start();
    poolSetMaxSize(pool, 3);
    x = finish(a);
    y = finish(b);
    if (!x || !y || x == y) abort();
    poolRelease(pool, held);
    poolRelease(pool, x);
    poolRelease(pool, y);
    if (poolFree(pool)) abort();
    return sem_destroy(&waiting) != 0;
}
