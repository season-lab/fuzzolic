#include <signal.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <time.h>

#include "solver.h"
#include "i386.h"

#define EXPR_QUEUE_POLLING_TIME_SECS 0
#define EXPR_QUEUE_POLLING_TIME_NS 5000

static int expr_pool_shm_id = -1;
Expr*      pool;

static int    query_shm_id = -1;
static Expr** next_query;

typedef struct SMTSolver {
    Z3_context ctx;
} SMTSolver;

SMTSolver smt_solver;

static uint8_t* testcase      = NULL;
static size_t   testcase_size = 0;

static void exitf(const char* message)
{
    fprintf(stderr, "BUG: %s.\n", message);
    exit(1);
}

#if Z3_VERSION <= 451
static void smt_error_handler(Z3_context c, Z3_error_code e)
#else
static void smt_error_handler(Z3_context c, Z3_error_code e)
#endif
{
#if Z3_VERSION <= 451
    printf("Error code: %s\n", Z3_get_error_msg(e));
#else
    printf("Error code: %s\n", Z3_get_error_msg(smt_solver.ctx, e));
#endif
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
static size_t cached_input_size = 0;
Z3_ast        smt_new_symbol(const char* name, size_t n_bits, Expr* e)
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
    cached_input_size = n_bits;
    return s;
}

Z3_ast smt_new_const(uint64_t value, size_t n_bits)
{
    Z3_sort bv_sort = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
    Z3_ast  s       = Z3_mk_unsigned_int64(smt_solver.ctx, value, bv_sort);
    return s;
}

static uint32_t file_next_id = 0;
static void     smt_dump_solution(Z3_model m)
{
    assert(cached_input);
    size_t input_size = cached_input_size / 8;

    char test_case_name[128];
    int n = snprintf(test_case_name, sizeof(test_case_name), "test_case_%u.dat",
                     file_next_id - 1);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    // SAYF("Dumping solution into %s\n", test_case_name);
    FILE* fp = fopen(test_case_name, "w");
#if 0
    for (long i = 0; i < input_size; i++) {
#else
    for (long i = input_size - 1; i >= 0; i--) {
#endif
    Z3_ast input_slice =
        Z3_mk_extract(smt_solver.ctx, (8 * (i + 1)) - 1, 8 * i, cached_input);
    Z3_ast  solution;
    Z3_bool successfulEval =
        Z3_model_eval(smt_solver.ctx, m, input_slice,
                      testcase ? Z3_FALSE : Z3_TRUE, // model_completion
                      &solution);
    assert(successfulEval && "Failed to evaluate model");
    assert(Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_NUMERAL_AST &&
           "Evaluated expression has wrong sort");
    int     solution_byte = 0;
    Z3_bool successGet =
        Z3_get_numeral_int(smt_solver.ctx, solution, &solution_byte);
    if (solution_byte)
        printf("Solution[%ld]: 0x%x\n", input_size - i - 1, solution_byte);
    else
        solution_byte = (input_size - i - 1) < testcase_size
                            ? testcase[input_size - i - 1]
                            : 0;
    fwrite(&solution_byte, sizeof(char), 1, fp);
}
fclose(fp);
}

static void inline smt_dump_solver(Z3_solver solver)
{
    Z3_string s_query = Z3_solver_to_string(smt_solver.ctx, solver);
    char      test_case_name[128];
    int       n = snprintf(test_case_name, sizeof(test_case_name),
                     "test_case_%u.query", file_next_id++);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    // SAYF("Dumping solution into %s\n", test_case_name);
    FILE* fp = fopen(test_case_name, "w");
    fwrite(s_query, strlen(s_query), 1, fp);
    fclose(fp);
}

static void smt_query_check(Z3_solver solver, Z3_ast query,
                            uint8_t preserve_solver)
{
    Z3_model m = 0;

    /* save the current state of the context */
    if (preserve_solver)
        Z3_solver_push(smt_solver.ctx, solver);

    Z3_solver_assert(smt_solver.ctx, solver, query);

    smt_dump_solver(solver);

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

void smt_print_ast_sort(Z3_ast e)
{
    Z3_sort sort = Z3_get_sort(smt_solver.ctx, e);
    printf("Sort: %s\n", Z3_sort_to_string(smt_solver.ctx, sort));
}

Z3_ast smt_bv_extract(Z3_ast e, size_t width)
{
    size_t high = (8 * width) - 1;
    size_t low = 0;
    return Z3_mk_extract(smt_solver.ctx, high, low, e);
}

Z3_ast smt_to_bv_n(Z3_ast e, size_t width) // cast boolean to a bitvector
{
    if (Z3_get_sort_kind(smt_solver.ctx, Z3_get_sort(smt_solver.ctx, e)) ==
        Z3_BOOL_SORT) {
        return Z3_mk_ite(smt_solver.ctx, e, smt_new_const(1, width * 8),
                         smt_new_const(0, width * 8));
    } else {
        return e;
    }
}

Z3_ast smt_to_bv(Z3_ast e)
{
    return smt_to_bv_n(e, 64);
}

#define VERBOSE 0
Z3_ast smt_query_to_z3(Expr* query, uintptr_t is_const, size_t width)
{
    if (width <= 0)
        width = sizeof(void*);

    if (is_const) {
        //printf("IS_CONST: %lx\n", (uintptr_t)query);
        return smt_new_const((uintptr_t)query, 8 * width);
    }

    if (query == NULL)
        return Z3_mk_true(smt_solver.ctx);

    Z3_ast   op1 = NULL;
    Z3_ast   op2 = NULL;
    Z3_ast   r   = NULL;
    unsigned n   = 0;
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            r   = Z3_mk_bvneg(smt_solver.ctx, op1);
            break;
        //
        case ADD:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
#if VERBOSE
            printf("ADD\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvadd(smt_solver.ctx, smt_to_bv(op1), smt_to_bv(op2));
            break;
        case SUB:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
#if VERBOSE
            printf("SUB\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvsub(smt_solver.ctx, op1, op2);
            break;
        case AND:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
#if VERBOSE
            printf("AND\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            if (Z3_get_sort_kind(smt_solver.ctx,
                                 Z3_get_sort(smt_solver.ctx, op1)) ==
                Z3_BOOL_SORT) {
                Z3_ast args[2] = {op1, op2};
                r              = Z3_mk_and(smt_solver.ctx, 2, args);
            } else
                r = Z3_mk_bvand(smt_solver.ctx, op1, op2);
            break;
        case XOR: // 13
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
            r   = Z3_mk_bvxor(smt_solver.ctx, op1, op2);
            break;
        case SHR: // 15
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
            r   = Z3_mk_bvlshr(smt_solver.ctx, op1, op2);
            break;
        case ROTL: // 17
            assert(query->op2_is_const && "Second arg of ROL must be concrete");
            op2     = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            int pos = (int)(long long)query->op2;
            r       = Z3_mk_rotate_left(smt_solver.ctx, pos, op2);
            break;
        //
        case EQ:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
#if VERBOSE
            printf("EQ\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_eq(smt_solver.ctx, smt_to_bv(op1), smt_to_bv(op2));
            break;
        case NE:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
#if VERBOSE
            printf("NE\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_not(smt_solver.ctx, Z3_mk_eq(smt_solver.ctx, smt_to_bv(op1), smt_to_bv(op2)));
            break;
        //
        case LT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
#if VERBOSE
            printf("LT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvslt(smt_solver.ctx, op1, op2);
            break;
        case GE:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
#if VERBOSE
            printf("LT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvsge(smt_solver.ctx, op1, op2);
            break;
        //
        case LTU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
#if VERBOSE
            printf("LTU\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvult(smt_solver.ctx, op1, op2);
            break;
        case LEU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
            r   = Z3_mk_bvule(smt_solver.ctx, op1, op2);
            break;
        case GEU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
            r   = Z3_mk_bvuge(smt_solver.ctx, op1, op2);
            break;
        case GTU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
            r   = Z3_mk_bvugt(smt_solver.ctx, op1, op2);
            break;
        //
        case ZEXT:
            op1        = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            unsigned n = (uintptr_t)query->op2;
            op1        = Z3_mk_extract(smt_solver.ctx, n - 1, 0, op1);
            op2        = smt_new_const(0, 64 - n);
#if VERBOSE
            printf("EXTRACT + ZEXT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_concat(smt_solver.ctx, op2, op1);
            // smt_print_ast_sort(r);
            break;
        case SEXT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            n   = (uintptr_t)query->op2;
            op1 = Z3_mk_extract(smt_solver.ctx, n - 1, 0, op1);
            r   = Z3_mk_sign_ext(smt_solver.ctx, 64 - n, op1);
            break;
        case CONCAT8:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0);
            r   = Z3_mk_concat(smt_solver.ctx, op1, op2);
            break;
        case EXTRACT8:
            op1           = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            unsigned high = ((((uintptr_t)query->op2) + 1) * 8) - 1;
            unsigned low  = ((uintptr_t)query->op2) * 8;
            r             = Z3_mk_extract(smt_solver.ctx, high, low, op1);
            break;

        // x86 specific
        case RCL:
        case CMPB:
        case PMOVMSKB:
        case EFLAGS_ALL_ADD:
        case EFLAGS_ALL_ADCB:
        case EFLAGS_ALL_ADCW:
        case EFLAGS_ALL_ADCL:
        case EFLAGS_ALL_ADCQ:
        case EFLAGS_ALL_SUB:
        case EFLAGS_ALL_MUL:
        case EFLAGS_ALL_SBBB:
        case EFLAGS_ALL_SBBW:
        case EFLAGS_ALL_SBBL:
        case EFLAGS_ALL_SBBQ:
        case EFLAGS_ALL_LOGIC:
        case EFLAGS_ALL_INC:
        case EFLAGS_ALL_DEC:
        case EFLAGS_ALL_SHL:
        case EFLAGS_ALL_SAR:
        case EFLAGS_ALL_BMILG:
        case EFLAGS_ALL_ADCX:
        case EFLAGS_ALL_ADCO:
        case EFLAGS_ALL_ADCOX:
        case EFLAGS_ALL_RCL:
        case EFLAGS_C_ADD:
        case EFLAGS_C_ADCB:
        case EFLAGS_C_ADCW:
        case EFLAGS_C_ADCL:
        case EFLAGS_C_ADCQ:
        case EFLAGS_C_SUB:
        case EFLAGS_C_MUL:
        case EFLAGS_C_SBBB:
        case EFLAGS_C_SBBW:
        case EFLAGS_C_SBBL:
        case EFLAGS_C_SBBQ:
        case EFLAGS_C_LOGIC:
        case EFLAGS_C_SHL:
            r = smt_query_i386_to_z3(smt_solver.ctx, query, is_const, width);
            break;

        default:
            ABORT("Unknown expr opkind: %u", query->opkind);
    }

    // printf("%s\n", Z3_ast_to_string(smt_solver.ctx, r));
    return r;
}

static void smt_query(Expr* query)
{
#if 0
    print_expr(query);
#endif

    Z3_solver solver = Z3_mk_solver(smt_solver.ctx);
    Z3_solver_inc_ref(smt_solver.ctx, solver);

    SAYF("Translating query to Z3...\n");
    Z3_ast z3_query = smt_query_to_z3(query, 0, 0);

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

static inline void smt_load_solver(const char* file)
{
    Z3_solver solver = Z3_mk_solver(smt_solver.ctx);
    Z3_solver_inc_ref(smt_solver.ctx, solver);
    Z3_ast query =
        Z3_parse_smtlib2_file(smt_solver.ctx, file, 0, 0, 0, 0, 0, 0);

    Z3_solver_assert(smt_solver.ctx, solver, query);

    Z3_model m = 0;
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
                // smt_dump_solution(m);
                printf("solution:\n %s\n",
                       Z3_model_to_string(smt_solver.ctx, m));
            }
            break;
    }
    if (m)
        Z3_model_dec_ref(smt_solver.ctx, m);

    Z3_solver_dec_ref(smt_solver.ctx, solver);
}

#if 0
#include "test.c"
#endif

static inline void load_testcase(const char* filename)
{
    printf("Loading testcase: %s\n", filename);
    char  data[1024 * 100] = {0};
    FILE* fp               = fopen(filename, "r");
    int   r                = fread(&data, 1, sizeof(data), fp);
    if (r == sizeof(data))
        PFATAL("Testcase is too large\n");
    printf("Loaded %d from testcase\n", r);
    assert(r > 0);
    testcase      = malloc(r);
    testcase_size = r;
    memmove(testcase, &data, r);
}

int main(int argc, char* argv[])
{
    smt_init();

#if 0
    test();
    return 0;
#endif

    if (argc < 3) {
        printf("%s <testcase> <testcase_dir> [-d]\n", argv[0]);
        printf("%s -q <testcase.query>\n", argv[0]);
        exit(1);
    }

    if (argc == 3 && strcmp("-q", argv[1]) == 0) {
        smt_load_solver(argv[2]);
        return 0;
    } else if (argc == 4 && strcmp("-d", argv[3]) == 0) {
        load_testcase(argv[1]);
    }

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