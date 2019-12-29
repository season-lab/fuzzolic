#include <stdint.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <unistd.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>

#include <z3.h>

#define USE_COLOR
#include "debug.h"

#define EXPR_QUEUE_POLLING_TIME_SECS 0
#define EXPR_QUEUE_POLLING_TIME_NS 5000

#include "../tracer/tcg/symbolic/symbolic-struct.h"

static int expr_pool_shm_id = -1;
Expr *pool;

static int query_shm_id = -1;
static Expr **next_query;

typedef struct SMTSolver
{
    Z3_context ctx;
} SMTSolver;

SMTSolver smt_solver;

static void exitf(const char *message)
{
    fprintf(stderr, "BUG: %s.\n", message);
    exit(1);
}

static void smt_error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

static void smt_init(void)
{
    Z3_config cfg = Z3_mk_config();
    //Z3_set_param_value(cfg, "model", "true");
    smt_solver.ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(smt_solver.ctx, smt_error_handler);
    Z3_del_config(cfg);
}

static void smt_destroy(void)
{
    assert(smt_solver.ctx);
    Z3_del_context(smt_solver.ctx);
}

static Z3_ast smt_new_symbolic(const char * name, size_t n_bytes)
{
    Z3_sort bv_sort = Z3_mk_bv_sort(smt_solver.ctx, 8 * n_bytes);
    Z3_symbol s_name = Z3_mk_string_symbol(smt_solver.ctx, name);
    Z3_ast s = Z3_mk_const(smt_solver.ctx, s_name, bv_sort);
    return s;
}

static int need_to_clean = 1;
static void cleanup(void)
{
    // signal handler and atexit data race...
    if (!need_to_clean)
        return;
    need_to_clean = 0;

    SAYF("Cleaning up...\n");
    smt_destroy();

    if (expr_pool_shm_id > 0)
        shmctl(expr_pool_shm_id, IPC_RMID, NULL);
    if (query_shm_id > 0)
        shmctl(query_shm_id, IPC_RMID, NULL);

    //SAYF("Deleted POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id, query_shm_id);
}

static void run_query(Expr *query)
{
    SAYF("\nRunning a query: %p\n", *next_query);
    print_expr(*next_query);
}

void sig_handler(int signo)
{
    cleanup();
    exit(0);
}

int main(int argc, char *argv[])
{
    smt_init();
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

    //SAYF("POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id, query_shm_id);

    // remove on exit
    atexit(cleanup);

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
    polling_time.tv_sec = EXPR_QUEUE_POLLING_TIME_SECS;
    polling_time.tv_nsec = EXPR_QUEUE_POLLING_TIME_NS;

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
            run_query(*next_query);
            next_query++;
        }
    }

    return 0;
}