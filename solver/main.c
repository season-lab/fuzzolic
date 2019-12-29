#include <stdint.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <unistd.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>

#define USE_COLOR
#include "debug.h"

#include "../qemu/tcg/symbolic/symbolic-struct.h"

static int expr_pool_shm_id = -1;
Expr *pool;

static int query_shm_id = -1;
static Expr **next_query;

static void del_shm(void)
{
    if (expr_pool_shm_id > 0)
        shmctl(expr_pool_shm_id, IPC_RMID, NULL);
    if (query_shm_id > 0)
        shmctl(query_shm_id, IPC_RMID, NULL);
    SAYF("Deleted POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id, query_shm_id);
}

void sig_handler(int signo)
{
    del_shm();
    exit(0);
}

int main(int argc, char *argv[])
{
    signal(SIGINT, sig_handler);

    expr_pool_shm_id = shmget(EXPR_POOL_SHM_KEY, // IPC_PRIVATE,
                              sizeof(Expr) * EXPR_POOL_CAPACITY,
                              IPC_CREAT | 0666); /*| IPC_EXCL */
    if (expr_pool_shm_id < 0)
        PFATAL("shmget() failed");

    query_shm_id = shmget(QUERY_SHM_KEY, // IPC_PRIVATE,
                          sizeof(Expr *) * EXPR_POOL_CAPACITY,
                          IPC_CREAT | 0666); /*| IPC_EXCL */
    if (query_shm_id < 0)
        PFATAL("shmget() failed");

    SAYF("POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id, query_shm_id);

    // remove on exit
    atexit(del_shm);

    pool = shmat(expr_pool_shm_id, EXPR_POOL_ADDR, 0);
    if (!pool)
        PFATAL("shmat() failed");

    next_query = shmat(query_shm_id, NULL, 0);
    if (!next_query)
        PFATAL("shmat() failed");

    // reset pool and query queue
    memset(pool, 0, sizeof(Expr) * EXPR_POOL_CAPACITY);
    memset(next_query, 0, sizeof(Expr *) * EXPR_POOL_CAPACITY);

    struct timespec polling_time;
    polling_time.tv_sec = 0;
    polling_time.tv_nsec = 5000;

    while (1)
    {
        if (*next_query == 0)
        {
            nanosleep(&polling_time, NULL);
        }
        else
        {
            if (*next_query == FINAL_QUERY)
            {
                SAYF("Reached final query. Exiting...\n");
                exit(0);
            }

            SAYF("Running a query: %p\n", *next_query);
            print_expr(*next_query);
            next_query++;
        }
    }

    return 0;
}