#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <time.h>
#include <unistd.h>

#include <z3.h>

#define USE_COLOR
#include "debug.h"

#define EXPR_QUEUE_POLLING_TIME_SECS 0
#define EXPR_QUEUE_POLLING_TIME_NS   5000

#include "../tracer/tcg/symbolic/symbolic-struct.h"

static int expr_pool_shm_id = -1;
Expr*      pool;

static int    query_shm_id = -1;
static Expr** next_query;

typedef struct SMTSolver {
    Z3_context ctx;
} SMTSolver;

SMTSolver smt_solver;

static void exitf(const char* message)
{
    fprintf(stderr, "BUG: %s.\n", message);
    exit(1);
}

static void smt_error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %s\n", Z3_get_error_msg(e));
    exitf("incorrect use of Z3");
}

static void smt_init(void)
{
    Z3_config cfg = Z3_mk_config();
    // Z3_set_param_value(cfg, "model", "true");
    smt_solver.ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(smt_solver.ctx, smt_error_handler);
    Z3_del_config(cfg);
}

static void smt_destroy(void)
{
    assert(smt_solver.ctx);
    Z3_del_context(smt_solver.ctx);
}

static Expr*  cached_input_expr = NULL;
static Z3_ast cached_input      = NULL;
static Z3_ast smt_new_symbol(const char* name, size_t n_bits, Expr* e)
{
    // ToDo: support more than one input
    if (cached_input) {
        assert(e->op1 == cached_input_expr->op1 &&
               e->op2 == cached_input_expr->op2);
        return cached_input;
    }

    Z3_sort   bv_sort = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
    Z3_symbol s_name  = Z3_mk_string_symbol(smt_solver.ctx, name);
    Z3_ast    s       = Z3_mk_const(smt_solver.ctx, s_name, bv_sort);
    cached_input      = s;
    cached_input_expr = e;
    return s;
}

static Z3_ast smt_new_const(uint64_t value, size_t n_bits)
{
    Z3_sort bv_sort = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
    Z3_ast  s       = Z3_mk_unsigned_int(smt_solver.ctx, value, bv_sort);
    return s;
}

static uint32_t file_next_id = 0;
static void     smt_dump_solution(Z3_model m)
{
    assert(cached_input);
    size_t input_size = (size_t)cached_input_expr->op2;

    char test_case_name[128];
    int n = snprintf(test_case_name, sizeof(test_case_name), "test_case_%u.dat", file_next_id++);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    //SAYF("Dumping solution into %s\n", test_case_name);
    FILE* fp = fopen(test_case_name, "w");
#if 1
    for (long i = 0; i < input_size; i++) {
#else
    for (long i = input_size - 1; i >= 0; i--) {
#endif
        Z3_ast  input_slice = Z3_mk_extract(smt_solver.ctx, (8 * (i + 1)) - 1,
                                           8 * i, cached_input);
        Z3_ast  solution;
        Z3_bool successfulEval =
            Z3_model_eval(smt_solver.ctx, m, input_slice,
                          /*model_completion=*/Z3_TRUE, &solution);
        assert(successfulEval && "Failed to evaluate model");
        assert(Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_NUMERAL_AST &&
               "Evaluated expression has wrong sort");
        int     solution_byte = 0;
        Z3_bool successGet =
            Z3_get_numeral_int(smt_solver.ctx, solution, &solution_byte);
        if (solution_byte)
            printf("Solution[%ld]: %x\n", i, solution_byte);
        fwrite(&solution_byte, sizeof(char), 1, fp);
    }
    fclose(fp);
}

static void smt_query_check(Z3_solver solver, Z3_ast query,
                            uint8_t preserve_solver)
{
    Z3_model m = 0;
    Z3_ast   not_f;

    /* save the current state of the context */
    if (preserve_solver)
        Z3_solver_push(smt_solver.ctx, solver);

    // not_f = Z3_mk_not(smt_solver.ctx, query);
    Z3_solver_assert(smt_solver.ctx, solver, query);

    switch (Z3_solver_check(smt_solver.ctx, solver)) {
        case Z3_L_FALSE:
            printf("Query is UNSAT\n");
            break;
        case Z3_L_UNDEF:
            /* Z3 failed to prove/disprove f. */
            printf("unknown\n");
            m = Z3_solver_get_model(smt_solver.ctx, solver);
            if (m != 0) {
                Z3_model_inc_ref(smt_solver.ctx, m);
                /* m should be viewed as a potential counterexample. */
                printf("potential counterexample:\n%s\n",
                       Z3_model_to_string(smt_solver.ctx, m));
            }
            break;
        case Z3_L_TRUE:
            printf("Query is SAT\n");
            m = Z3_solver_get_model(smt_solver.ctx, solver);
            if (m) {
                Z3_model_inc_ref(smt_solver.ctx, m);
                smt_dump_solution(m);
                // printf("solution:\n %s\n",
                // Z3_model_to_string(smt_solver.ctx, m));
            }
            break;
    }
    if (m)
        Z3_model_dec_ref(smt_solver.ctx, m);

    /* restore scope */
    if (preserve_solver)
        Z3_solver_pop(smt_solver.ctx, solver, 1);
}

static inline void smt_print_ast_sort(Z3_ast e)
{
    Z3_sort sort = Z3_get_sort(smt_solver.ctx, e);
    //printf("Sort: %s\n", Z3_sort_to_string(smt_solver.ctx, sort));
}

static Z3_ast smt_query_to_z3(Expr* query, uintptr_t is_const)
{
    if (is_const)
        return smt_new_const((uintptr_t)query, 64);

    if (query == NULL)
        return Z3_mk_true(smt_solver.ctx);

    Z3_ast op1 = NULL;
    Z3_ast op2 = NULL;
    Z3_ast r   = NULL;
    switch (query->opkind) {
        case RESERVED:
            ABORT("Invalid opkind (RESERVER). There is a bug somewhere :(");
        case IS_SYMBOLIC:;
            // ToDo: get name and size from the struct
            char* input_name = malloc(16);
            snprintf(input_name, 16, "input_%lu", (uintptr_t)query->op1);
            r = smt_new_symbol(input_name, 8 * (uintptr_t)query->op2, query);
            break;
        case IS_CONST:
            r = smt_new_const((uintptr_t)query->op1, 64);
            break;
        //
        case NEG:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            r   = Z3_mk_bvneg(smt_solver.ctx, op1);
            break;
        //
        case ADD:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            r   = Z3_mk_bvadd(smt_solver.ctx, op1, op2);
            break;
        case SUB:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            r   = Z3_mk_bvsub(smt_solver.ctx, op1, op2);
            break;
        case AND:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            // printf("AND\n");
            // smt_print_ast_sort(op1);
            // smt_print_ast_sort(op2);
            if (Z3_get_sort_kind(smt_solver.ctx,
                                 Z3_get_sort(smt_solver.ctx, op1)) ==
                Z3_BOOL_SORT) {
                Z3_ast args[2] = {op1, op2};
                r              = Z3_mk_and(smt_solver.ctx, 2, args);
            } else
                r = Z3_mk_bvand(smt_solver.ctx, op1, op2);
            break;
        //
        case EQ:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            // printf("EQ\n");
            // smt_print_ast_sort(op1);
            // smt_print_ast_sort(op2);
            r = Z3_mk_eq(smt_solver.ctx, op1, op2);
            break;
        case NE:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            // printf("NE\n");
            // smt_print_ast_sort(op1);
            // smt_print_ast_sort(op2);
            r = Z3_mk_not(smt_solver.ctx, Z3_mk_eq(smt_solver.ctx, op1, op2));
            break;
        //
        case LTU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            r   = Z3_mk_bvult(smt_solver.ctx, op1, op2);
            break;
        case LEU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            r   = Z3_mk_bvule(smt_solver.ctx, op1, op2);
            break;
        case GEU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            r   = Z3_mk_bvuge(smt_solver.ctx, op1, op2);
            break;
        case GTU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            r   = Z3_mk_bvugt(smt_solver.ctx, op1, op2);
            break;
        //
        case ZEXT:
            op1        = smt_query_to_z3(query->op1, query->op1_is_const);
            unsigned n = (uintptr_t)query->op2;
            op1        = Z3_mk_extract(smt_solver.ctx, n - 1, 0, op1);
            op2        = smt_new_const(0, 64 - n);
            r          = Z3_mk_concat(smt_solver.ctx, op2, op1);
            break;
        //
        case CONCAT8:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const);
            r   = Z3_mk_concat(smt_solver.ctx, op1, op2);
            break;
        case EXTRACT8:
            op1           = smt_query_to_z3(query->op1, query->op1_is_const);
            unsigned high = ((((uintptr_t)query->op2) + 1) * 8) - 1;
            unsigned low  = ((uintptr_t)query->op2) * 8;
            r             = Z3_mk_extract(smt_solver.ctx, high, low, op1);
            break;
        default:
            ABORT("Unknown expr opkind: %u", query->opkind);
    }

    // printf("%s\n", Z3_ast_to_string(smt_solver.ctx, r));
    return r;
}

static void smt_query(Expr* query)
{
    //print_expr(query);

    Z3_solver solver = Z3_mk_solver(smt_solver.ctx);
    Z3_solver_inc_ref(smt_solver.ctx, solver);

    SAYF("Translating query to Z3...\n");
    Z3_ast z3_query = smt_query_to_z3(query, 0);

    SAYF("DONE: Translating query to Z3\n");
#if 0
    Z3_set_ast_print_mode(smt_solver.ctx, Z3_PRINT_LOW_LEVEL);
    const char * z3_query_str = Z3_ast_to_string(smt_solver.ctx, z3_query);
    SAYF("%s\n", z3_query_str);
#endif

    SAYF("Running a query...\n");
    smt_query_check(solver, z3_query, 0);

    Z3_solver_dec_ref(smt_solver.ctx, solver);
}

static int  need_to_clean = 1;
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

    // SAYF("Deleted POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id,
    // query_shm_id);
}

void sig_handler(int signo)
{
    cleanup();
    exit(0);
}
#if 0
static void test(void)
{
    Z3_ast input = smt_new_symbol("input", 64);

    Z3_ast b0 = Z3_mk_extract(smt_solver.ctx, 7, 0, input);
    Z3_ast b1 = Z3_mk_extract(smt_solver.ctx, 15, 8, input);
    Z3_ast b2 = Z3_mk_extract(smt_solver.ctx, 23, 16, input);
    Z3_ast b3 = Z3_mk_extract(smt_solver.ctx, 31, 24, input);

    Z3_ast r = Z3_mk_concat(smt_solver.ctx, b1, b0);
    r = Z3_mk_concat(smt_solver.ctx, b2, r);
    r = Z3_mk_concat(smt_solver.ctx, b3, r);

    //r = Z3_mk_extract(smt_solver.ctx, 31, 0, r);

    Z3_ast zero32 = smt_new_const(0, 32);
    Z3_ast merged = Z3_mk_concat(smt_solver.ctx, zero32, r);

    Z3_ast deadbeef = smt_new_const(0xdeadbeef, 64);

    r = Z3_mk_bvsub(smt_solver.ctx, merged, deadbeef);

    Z3_ast zero64 = smt_new_const(0, 64);
    Z3_ast z3_query = Z3_mk_eq(smt_solver.ctx, r, zero64);

    Z3_solver solver = Z3_mk_solver(smt_solver.ctx);
    Z3_solver_inc_ref(smt_solver.ctx, solver);

    const char * z3_query_str = Z3_ast_to_string(smt_solver.ctx, z3_query);
    SAYF("%s\n", z3_query_str);

    smt_query_check(solver, z3_query, 0);

    Z3_solver_dec_ref(smt_solver.ctx, solver);
}
#endif

int main(int argc, char* argv[])
{
    smt_init();
    signal(SIGINT, sig_handler);

    expr_pool_shm_id = shmget(EXPR_POOL_SHM_KEY, // IPC_PRIVATE,
                              sizeof(Expr) * EXPR_POOL_CAPACITY,
                              IPC_CREAT | 0666); /*| IPC_EXCL */
    if (expr_pool_shm_id < 0)
        PFATAL("shmget() failed");

    query_shm_id = shmget(QUERY_SHM_KEY, // IPC_PRIVATE,
                          sizeof(Expr*) * EXPR_POOL_CAPACITY,
                          IPC_CREAT | 0666); /*| IPC_EXCL */
    if (query_shm_id < 0)
        PFATAL("shmget() failed");

    // SAYF("POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id,
    // query_shm_id);

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
    memset(next_query, 0, sizeof(Expr*) * EXPR_POOL_CAPACITY);

    struct timespec polling_time;
    polling_time.tv_sec  = EXPR_QUEUE_POLLING_TIME_SECS;
    polling_time.tv_nsec = EXPR_QUEUE_POLLING_TIME_NS;

    while (1) {
        if (*next_query == 0) {
            nanosleep(&polling_time, NULL);
        } else {
            if (*next_query == FINAL_QUERY) {
                SAYF("Reached final query. Exiting...\n");
                exit(0);
            }
            smt_query(*next_query);
            next_query++;
        }
    }

    return 0;
}