#include <stdint.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <unistd.h>
#include <signal.h>

#define USE_COLOR
#include "debug.h"

#include "../qemu/tcg/symbolic/symbolic-struct.h"

static int expr_pool_shm_id = -1;
static Expr * pool;

static void del_shm(void)
{
    if (expr_pool_shm_id > 0)
        shmctl(expr_pool_shm_id, IPC_RMID, NULL);
    SAYF("Deleting POOL_SHM_ID=%d\n", expr_pool_shm_id);
}

void sig_handler(int signo)
{
    del_shm();
}

int main(int argc, char *argv[])
{

    signal(SIGINT, sig_handler);

    expr_pool_shm_id = shmget(EXPR_POOL_SHM_KEY, // IPC_PRIVATE,
                              sizeof(Expr) * EXPR_POOL_CAPACITY,
                              IPC_CREAT /*| IPC_EXCL */ | 0600);
    if (expr_pool_shm_id < 0)
        PFATAL("shmget() failed");

    SAYF("POOL_SHM_ID=%d\n", expr_pool_shm_id);
    atexit(del_shm);

    pool = shmat(expr_pool_shm_id, NULL, 0);
    if (!pool)
        PFATAL("shmat() failed");

    memset(pool, 0, sizeof(Expr) * EXPR_POOL_CAPACITY);
    sleep(3600);

    return 0;
}