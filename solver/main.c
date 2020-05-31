#include <signal.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <execinfo.h>

#include "solver.h"
#include "i386.h"
#include "fuzzy-sat/z3-fuzzy.h"

#define EXPR_QUEUE_POLLING_TIME_SECS 0
#define EXPR_QUEUE_POLLING_TIME_NS   5000
#define SOLVER_TIMEOUT_MS            10000
#define FUZZ_SLICE_ADDRESS           1

#define DEBUG_FUZZ_EXPR 0
#define DEBUG_EXPR_OPT  0
#define DISABLE_SMT     0

#ifndef USE_FUZZY_SOLVER
#define USE_FUZZY_SOLVER 0
#endif

static int go_signal        = 0;
static int expr_pool_shm_id = -1;
Expr*      pool;

static int    query_shm_id = -1;
static Query* next_query;
static Query* query_queue;

uint8_t* branch_bitmap = NULL;

#if BRANCH_COVERAGE == FUZZOLIC
static int bitmap_shm_id = -1;
#endif

GHashTable* z3_expr_cache;

void print_z3_ast(Z3_ast e);

typedef struct SMTSolver {
    Z3_context ctx;
    uint64_t   sat_count;
    uint64_t   sat_time;
    uint64_t   unsat_count;
    uint64_t   unsat_time;
    uint64_t   unknown_count;
    uint64_t   unknown_time;
    uint64_t   translation_time;
    uint64_t   expr_visit_time;
    uint64_t   slice_reasoning_time;
#if USE_FUZZY_SOLVER
    fuzzy_ctx_t fuzzy_ctx;
#endif
} SMTSolver;

static SMTSolver smt_solver;

typedef struct Dependency {
    GHashTable* inputs;
    GHashTable* exprs;
} Dependency;

#define MAX_INPUTS_EXPRS MAX_INPUT_SIZE * 16
static Z3_ast      input_exprs[MAX_INPUTS_EXPRS]        = {NULL};
static Z3_ast      z3_ast_exprs[EXPR_QUERY_CAPACITY]    = {0};
static Dependency* dependency_graph[MAX_INPUT_SIZE * 2] = {0};

static GHashTable* concretized_bytes                           = NULL;
static uint8_t     concretized_sloads[MAX_INPUTS_EXPRS]        = {0};
static Z3_ast      concretized_iloads[MAX_INPUTS_EXPRS]        = {0};
static GSList*     sloads_exprs                                = NULL;

typedef struct {
    size_t index;
    Z3_ast expr;
} SLoad;

typedef struct {
    uint8_t* data;
    size_t   size;
} Testcase;

static Testcase testcase;

#define APP(e)    ((Z3_app)e)
#define N_ARGS(e) Z3_get_app_num_args(smt_solver.ctx, APP(e))
#define ARG1(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 0)
#define ARG2(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 1)
#define ARG3(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 2)
#define ARG(e, i) Z3_get_app_arg(smt_solver.ctx, APP(e), i)
#define PARAM1(e)                                                              \
    Z3_get_decl_int_parameter(smt_solver.ctx,                                  \
                              Z3_get_app_decl(smt_solver.ctx, APP(e)), 0)
#define PARAM2(e)                                                              \
    Z3_get_decl_int_parameter(smt_solver.ctx,                                  \
                              Z3_get_app_decl(smt_solver.ctx, APP(e)), 1)
#define PARAM(e, i)                                                            \
    Z3_get_decl_int_parameter(smt_solver.ctx,                                  \
                              Z3_get_app_decl(smt_solver.ctx, APP(e)), i)
#define OP(e) get_op(APP(e))
#define SIZE(e)                                                                \
    Z3_get_bv_sort_size(smt_solver.ctx, Z3_get_sort(smt_solver.ctx, e))
#define IS_BOOL(e)                                                             \
    (Z3_get_sort_kind(smt_solver.ctx, Z3_get_sort(smt_solver.ctx, e)) ==       \
     Z3_BOOL_SORT)

Config config = {0};

static uint64_t conc_eval_time  = 0;
static uint64_t conc_eval_count = 0;
static uint8_t  symbols_sizes[MAX_INPUTS_EXPRS];
static uint64_t symbols_count = 0;
static uint64_t unsat_time    = 0;
static uint64_t unsat_count   = 0;
static uint64_t eval_data[MAX_INPUTS_EXPRS];

uint64_t conc_query_eval_value(Z3_context ctx, Z3_ast query, uint64_t* data,
                               uint8_t* symbols_sizes, size_t size);

static void exitf(const char* message)
{
    // fprintf(stderr, "BUG: %s\n", message);
    printf("BUG: %s\n", message);
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

static size_t get_input_size(const char* fname)
{
    assert(testcase.size > 0);
    return testcase.size;
}

static inline void get_time(struct timespec* tp)
{
    clockid_t clk_id = CLOCK_MONOTONIC;
    int       result = clock_gettime(clk_id, tp);
}

static inline uint64_t get_diff_time_microsec(struct timespec* start,
                                              struct timespec* end)
{
    uint64_t r = (end->tv_sec - start->tv_sec) * 1000000000;
    r += (end->tv_nsec - start->tv_nsec);
    return (r / 1000);
}

void print_trace(void)
{
    void*  array[10];
    size_t size;
    char** strings;
    size_t i;

    size    = backtrace(array, 10);
    strings = backtrace_symbols(array, size);

    printf("Obtained %zd stack frames.\n", size);

    for (i = 0; i < size; i++)
        printf("%s\n", strings[i]);

    free(strings);
}

static void smt_init(void)
{
    Z3_config cfg  = Z3_mk_config();
    smt_solver.ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(smt_solver.ctx, smt_error_handler);
    Z3_del_config(cfg);
#if 0
    char ts[32];
    sprintf(ts, "%u", SOLVER_TIMEOUT_MS);
    Z3_global_param_set("timeout", ts);
#endif
    z3_expr_cache = g_hash_table_new(NULL, NULL);

#if USE_FUZZY_SOLVER
    z3fuzz_init(&smt_solver.fuzzy_ctx, smt_solver.ctx,
                (char*)config.testcase_path, NULL, &conc_query_eval_value,
                SOLVER_TIMEOUT_MS);
#endif
}

static Z3_solver        cached_solver = NULL;
static inline Z3_solver smt_new_solver()
{
    if (cached_solver) {
        return cached_solver;
    }
#if 1
    cached_solver = Z3_mk_solver(smt_solver.ctx);
#else
    Z3_solver solver = Z3_mk_simple_solver(smt_solver.ctx);
#endif
    Z3_solver_inc_ref(smt_solver.ctx, cached_solver);
#if 1
    Z3_symbol timeout = Z3_mk_string_symbol(smt_solver.ctx, "timeout");
    Z3_params params  = Z3_mk_params(smt_solver.ctx);
    Z3_params_set_uint(smt_solver.ctx, params, timeout, SOLVER_TIMEOUT_MS);
    Z3_solver_set_params(smt_solver.ctx, cached_solver, params);
#endif
    return cached_solver;
}

static inline void smt_del_solver(Z3_solver solver)
{
#if 1
    Z3_solver_reset(smt_solver.ctx, solver);
#else
    Z3_solver_dec_ref(smt_solver.ctx, solver);
#endif
}

static inline void smt_destroy(void)
{
#if USE_FUZZY_SOLVER
    // z3fuzz_free(&smt_solver.fuzzy_ctx);
#endif
    if (smt_solver.ctx) {
        Z3_del_context(smt_solver.ctx);
    }
    g_hash_table_destroy(z3_expr_cache);
}

void print_z3_original(Z3_ast e)
{
    Z3_set_ast_print_mode(smt_solver.ctx, Z3_PRINT_LOW_LEVEL);
    const char* z3_query_str = Z3_ast_to_string(smt_solver.ctx, e);
    SAYF("\n%s\n", z3_query_str);
}

static inline void update_and_add_deps_to_solver(GHashTable* inputs,
                                                 size_t      query_idx,
                                                 Z3_solver solver, Z3_ast* deps)
{
    GHashTableIter iter, iter2;
    gpointer       key, value;
    gboolean       res;

    GHashTable* to_be_deallocated = g_hash_table_new(NULL, NULL);
    Dependency* current           = NULL;

    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {

        // printf("Checking deps for input %lu\n", (size_t)key);

        size_t      input_idx = (size_t)key;
        Dependency* dep       = dependency_graph[input_idx];
        if (dep && dep == current) {
            continue;
        } else if (current == NULL) {
            if (dep) {
                current = dep;
            } else {
                current         = malloc(sizeof(Dependency));
                current->inputs = g_hash_table_new(NULL, NULL);
                current->exprs  = g_hash_table_new(NULL, NULL);
                res             = g_hash_table_add(current->inputs, key);
                assert(res == TRUE);
            }
        } else if (dep == NULL) {
            g_hash_table_add(current->inputs, key);
        } else if (g_hash_table_contains(to_be_deallocated, dep) == TRUE) {
            assert(dep && current && dep != current);
            // already merged into current
        } else {
            // we have to merge current and dep
            assert(dep && current && dep != current);
            // merge inputs
            g_hash_table_iter_init(&iter2, dep->inputs);
            while (g_hash_table_iter_next(&iter2, &key, &value)) {
                g_hash_table_add(current->inputs, key);
            }
            // merge exprs
            g_hash_table_iter_init(&iter2, dep->exprs);
            while (g_hash_table_iter_next(&iter2, &key, &value)) {
                g_hash_table_add(current->exprs, key);
            }
            // deallocate later
            g_hash_table_add(to_be_deallocated, dep);
        }
    }

    // add exprs as assertions
    if (solver) {
        g_hash_table_iter_init(&iter, current->exprs);
        while (g_hash_table_iter_next(&iter, &key, &value)) {
            size_t query_dep_idx = (size_t)key;
            assert(z3_ast_exprs[query_dep_idx]);
            Z3_solver_assert(
                smt_solver.ctx, solver,
                // Z3_simplify(smt_solver.ctx, z3_ast_exprs[query_dep_idx]));
                z3_ast_exprs[query_dep_idx]);
            // printf("Adding expr %lu for %lu\n", query_dep_idx, query_idx);
            // printf("[%lu]: ", query_dep_idx);
            // print_z3_ast(z3_ast_exprs[query_dep_idx]);
            // print_z3_original(z3_ast_exprs[query_dep_idx]);
        }
    }

    if (deps) {
        if (g_hash_table_size(current->exprs) > 0) {
            Z3_ast* and_args =
                malloc(sizeof(Z3_ast) * g_hash_table_size(current->exprs));
            size_t k = 0;
            g_hash_table_iter_init(&iter, current->exprs);
            while (g_hash_table_iter_next(&iter, &key, &value)) {
                size_t query_dep_idx = (size_t)key;
                assert(z3_ast_exprs[query_dep_idx]);
                and_args[k++] = z3_ast_exprs[query_dep_idx];
                // printf("Adding expr %lu for %lu\n", query_dep_idx,
                // query_idx);
            }
            *deps = Z3_mk_and(smt_solver.ctx, g_hash_table_size(current->exprs),
                              and_args);
            free(and_args);
        } else {
            *deps = Z3_mk_true(smt_solver.ctx);
        }
    }

    res = g_hash_table_add(current->exprs, (gpointer)query_idx);
    assert(res == TRUE);

    // update dependency graph for each input in current
    g_hash_table_iter_init(&iter, current->inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        size_t input_idx            = (size_t)key;
        dependency_graph[input_idx] = current;
        // printf("Update dep list for input %lu\n", input_idx);
    }

    // housekeeping
    g_hash_table_iter_init(&iter, to_be_deallocated);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        Dependency* dep = (Dependency*)key;
        g_hash_table_destroy(dep->inputs);
        g_hash_table_destroy(dep->exprs);
        free(dep);
    }
    g_hash_table_destroy(to_be_deallocated);
}

static inline void add_deps_to_solver(GHashTable* inputs, Z3_solver solver)
{
    GHashTableIter iter, iter2;
    gpointer       key, value;
    gboolean       res;

    GHashTable* added_exprs = g_hash_table_new(NULL, NULL);

    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        size_t      input_idx = (size_t)key;
        Dependency* dep       = dependency_graph[input_idx];

        // printf("Input: %lu\n", input_idx);

        if (!dep) {
            continue;
        }
#if 0
        g_hash_table_iter_init(&iter2, dep->inputs);
        while (g_hash_table_iter_next(&iter2, &key, &value)) {
            printf("Input 2: %lu\n", key);
        }
#endif
        g_hash_table_iter_init(&iter2, dep->exprs);
        while (g_hash_table_iter_next(&iter2, &key, &value)) {
            // ToDo: can we remove this check?
            if (g_hash_table_contains(added_exprs, key) != TRUE) {
                g_hash_table_add(added_exprs, key);
                size_t query_dep_idx = (size_t)key;
                assert(z3_ast_exprs[query_dep_idx]);
                Z3_solver_assert(smt_solver.ctx, solver,
                                 z3_ast_exprs[query_dep_idx]);
            }
        }
    }

    g_hash_table_destroy(added_exprs);
}

static inline Z3_ast get_deps(GHashTable* inputs)
{
    assert(inputs);
    Z3_ast r = NULL;

    GHashTableIter iter, iter2;
    gpointer       key, value;
    gboolean       res;

    GHashTable* added_exprs = g_hash_table_new(NULL, NULL);
#if 0
    GHashTable* added_inputs = g_hash_table_new(NULL, NULL);
#endif
    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        size_t      input_idx = (size_t)key;
        Dependency* dep       = dependency_graph[input_idx];

        // printf("DEPS: Input_%lu\n", input_idx);

        if (!dep) {
            continue;
        }
#if 0
        g_hash_table_iter_init(&iter2, dep->inputs);
        while (g_hash_table_iter_next(&iter2, &key, &value)) {
            g_hash_table_add(added_inputs, key);
        }
#endif
        g_hash_table_iter_init(&iter2, dep->exprs);
        while (g_hash_table_iter_next(&iter2, &key, &value)) {
            // ToDo: can we remove this check?
            if (g_hash_table_contains(added_exprs, key) != TRUE) {
                g_hash_table_add(added_exprs, key);
                size_t query_dep_idx = (size_t)key;
                assert(z3_ast_exprs[query_dep_idx]);
                if (!r) {
                    r = z3_ast_exprs[query_dep_idx];
                } else {
                    Z3_ast args[2] = {r, z3_ast_exprs[query_dep_idx]};
                    r              = Z3_mk_and(smt_solver.ctx, 2, args);
                }
            }
        }
    }

    if (r == NULL) {
        r = Z3_mk_true(smt_solver.ctx);
    }
#if 0
    g_hash_table_iter_init(&iter2, added_inputs);
    while (g_hash_table_iter_next(&iter2, &key, &value)) {
        g_hash_table_add(inputs, key);
    }

    g_hash_table_destroy(added_inputs);
#endif
    g_hash_table_destroy(added_exprs);
    return r;
}

static Z3_ast z3_new_symbol(const char* name, size_t n_bits)
{
    Z3_sort   bv_sort = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
    Z3_symbol s_name  = Z3_mk_string_symbol(smt_solver.ctx, name);
    Z3_ast    s       = Z3_mk_const(smt_solver.ctx, s_name, bv_sort);
    return s;
}

static Z3_ast z3_new_symbol_int(int id, size_t n_bits)
{
    Z3_sort   bv_sort = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
    Z3_symbol s       = Z3_mk_int_symbol(smt_solver.ctx, id);
    Z3_ast    e       = Z3_mk_const(smt_solver.ctx, s, bv_sort);
    return e;
}

Z3_ast smt_new_symbol(uintptr_t id, const char* name, size_t n_bits, Expr* e)
{
    assert(id < MAX_INPUTS_EXPRS);
    if (id < testcase.size) {
        assert(n_bits == 8 && "Multi-byte input not yet supported.");
    }
    Z3_ast s = input_exprs[id];
    if (s == NULL) {
        s               = z3_new_symbol(name, n_bits);
        input_exprs[id] = s;
    }
    return s;
}

Z3_ast smt_new_symbol_int(uintptr_t id, size_t n_bits, Expr* e)
{
    assert(id < MAX_INPUTS_EXPRS);
    if (id < testcase.size) {
        assert(n_bits == 8 && "Multi-byte input not yet supported.");
    }
    Z3_ast s = input_exprs[id];
    if (s == NULL) {
        s               = z3_new_symbol_int(id, n_bits);
        input_exprs[id] = s;
    }
    return s;
}

Z3_ast smt_new_const(uint64_t value, size_t n_bits)
{
    Z3_sort bv_sort = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
    Z3_ast  s       = Z3_mk_unsigned_int64(smt_solver.ctx, value, bv_sort);
    return s;
}

static void smt_dump_solution(Z3_context ctx, Z3_model m, size_t idx,
                              size_t sub_idx)
{
    size_t input_size = testcase.size;

    char testcase_name[128];
    int  n = snprintf(testcase_name, sizeof(testcase_name),
                     "test_case_%lu_%lu.dat", idx, sub_idx);
    assert(n > 0 && n < sizeof(testcase_name) && "test case name too long");

#if 0
    SAYF("Dumping solution into %s\n", testcase_name);
#endif

    char    var_name[128];
    Z3_sort bv_sort = Z3_mk_bv_sort(ctx, 8);
    FILE*   fp      = fopen(testcase_name, "w");
    for (long i = 0; i < input_size; i++) {
#if 0
        int n = snprintf(var_name, sizeof(var_name), "k!%lu", i);
        assert(n > 0 && n < sizeof(var_name) && "symbol name too long");
        Z3_symbol s    = Z3_mk_string_symbol(ctx, var_name);
        Z3_ast input_slice   = Z3_mk_const(ctx, s, bv_sort);
#else
        Z3_ast input_slice = input_exprs[i];
#endif
        int solution_byte = 0;
        if (input_slice) {
            // SAYF("input slice %ld\n", i);
            Z3_ast  solution;
            Z3_bool successfulEval = Z3_model_eval(ctx, m, input_slice,
                                                   Z3_FALSE, // model_completion
                                                   &solution);
            assert(successfulEval && "Failed to evaluate model");
            if (Z3_get_ast_kind(ctx, solution) == Z3_NUMERAL_AST) {
                Z3_bool successGet =
                    Z3_get_numeral_int(ctx, solution, &solution_byte);
                if (successGet) // && solution_byte
                    printf("Solution[%ld]: 0x%x\n", i, solution_byte);
            } else {
                assert(Z3_get_ast_kind(ctx, solution) == Z3_APP_AST);
                solution_byte = i < testcase.size ? testcase.data[i] : 0;
            }
        } else {
            // printf("Input slice is not used by the formula\n");
            solution_byte = i < testcase.size ? testcase.data[i] : 0;
        }
        fwrite(&solution_byte, sizeof(char), 1, fp);
    }
    fclose(fp);
}

static void smt_dump_testcase(const uint8_t* data, size_t size, size_t stride,
                              size_t idx, size_t sub_idx)
{

    char testcase_name[128];
    int  n = snprintf(testcase_name, sizeof(testcase_name),
                     "test_case_%lu_%lu.dat", idx, sub_idx);
    assert(n > 0 && n < sizeof(testcase_name) && "test case name too long");

#if 0
    SAYF("Dumping solution into %s\n", testcase_name);
#endif

    FILE* fp = fopen(testcase_name, "w");
    for (size_t i = 0; i < size * stride; i += stride) {
        uint8_t byte = data[i];
        if (byte != testcase.data[i / stride]) {
            printf("Solution[%ld]: 0x%x\n", i / stride, byte);
        }
        fwrite(&byte, sizeof(char), 1, fp);
    }
    fclose(fp);
}

static int inline smt_run_from_string(Z3_solver source_solver, uintptr_t idx)
// static int inline smt_run_from_file(char * path)
{
    Z3_string s_query_orig = Z3_solver_to_string(smt_solver.ctx, source_solver);
#if 0
    FILE* fp = fopen("temp.query", "w");
    fwrite(s_query_orig, strlen(s_query_orig), 1, fp);
    fclose(fp);
#endif
    Z3_config  cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
#if 0
    Z3_ast_vector queries =
        Z3_parse_smtlib2_file(ctx, path, 0, 0, 0, 0, 0, 0);
#else
    Z3_ast_vector queries =
        Z3_parse_smtlib2_string(ctx, s_query_orig, 0, 0, 0, 0, 0, 0);
#endif
    Z3_ast_vector_inc_ref(ctx, queries);
    unsigned num_queries = Z3_ast_vector_size(ctx, queries);

    // Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver solver = Z3_mk_simple_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);

    Z3_global_param_set("timeout", "10000");
#if 0
    Z3_symbol timeout = Z3_mk_string_symbol(ctx, "timeout");
    Z3_params params  = Z3_mk_params(ctx);
    Z3_params_set_uint(ctx, params, timeout, SOLVER_TIMEOUT_MS);
    Z3_solver_set_params(ctx, solver, params);
#endif

    for (size_t i = 0; i < num_queries; i++) {
        Z3_ast query = Z3_ast_vector_get(ctx, queries, i);
        Z3_inc_ref(ctx, query);
        Z3_solver_assert(ctx, solver, query);
    }

    struct timespec start;
    get_time(&start);

    int      r   = 0;
    Z3_lbool res = Z3_solver_check(ctx, solver);
    if (res == Z3_L_TRUE) {
        printf("Query is SAT\n");
        r = 1;
#if 0
        Z3_model m = Z3_solver_get_model(smt_solver.ctx, solver);
        if (m) {
            Z3_model_inc_ref(ctx, m);
            smt_dump_solution(ctx, m, idx, 0);
        }
#endif
    } else if (res == Z3_L_FALSE) {
        printf("Query is UNSAT\n");
    } else {
        printf("Query is UNKNOWN\n");
    }

    struct timespec end;
    get_time(&end);
    uint64_t elapsed_microsecs = get_diff_time_microsec(&start, &end);

    printf("SMT FROM FILE: elapsed=%lu ms\n", elapsed_microsecs / 1000);

    for (size_t i = 0; i < num_queries; i++) {
        Z3_ast query = Z3_ast_vector_get(ctx, queries, i);
        Z3_dec_ref(ctx, query);
    }

    Z3_del_config(cfg);
    Z3_ast_vector_dec_ref(ctx, queries);
    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);

    return r;
}

static void inline smt_dump_solver_to_file(Z3_solver solver, char* path)
{
    Z3_string s_query = Z3_solver_to_string(smt_solver.ctx, solver);
    FILE*     fp      = fopen(path, "w");
    fwrite(s_query, strlen(s_query), 1, fp);
    fclose(fp);
}

#if DEBUG_FUZZ_EXPR
static void inline smt_dump_debug_query(Z3_solver pi, Z3_ast expr, uint64_t idx)
{
    Z3_string s_query = Z3_solver_to_string(smt_solver.ctx, pi);
    char      test_case_name[128];
    int       n =
        snprintf(test_case_name, sizeof(test_case_name), "debug_%lu.pi", idx);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    FILE* fp = fopen(test_case_name, "w");
    fwrite(s_query, strlen(s_query), 1, fp);
    fclose(fp);
    //
    Z3_solver_reset(smt_solver.ctx, pi);
    expr = Z3_mk_eq(smt_solver.ctx, expr, smt_new_const(0, SIZE(expr)));
    Z3_solver_assert(smt_solver.ctx, pi, expr);
    s_query = Z3_solver_to_string(smt_solver.ctx, pi);
    n = snprintf(test_case_name, sizeof(test_case_name), "debug_%lu.expr", idx);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    fp = fopen(test_case_name, "w");
    fwrite(s_query, strlen(s_query), 1, fp);
    fclose(fp);
}
#endif

static void inline smt_dump_solver(Z3_solver solver, size_t idx)
{
    Z3_string s_query = Z3_solver_to_string(smt_solver.ctx, solver);
    char      test_case_name[128];
    int       n = snprintf(test_case_name, sizeof(test_case_name),
                     "test_case_%lu.query", idx);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    // SAYF("Dumping solution into %s\n", test_case_name);
    FILE* fp = fopen(test_case_name, "w");
    fwrite(s_query, strlen(s_query), 1, fp);
    fclose(fp);
}

static int smt_query_check(Z3_solver solver, size_t idx, uint8_t optimistic)
{
    int             qres = 0;
    struct timespec start;
    get_time(&start);

    Z3_model m   = NULL;
    Z3_lbool res = Z3_solver_check(smt_solver.ctx, solver);

    struct timespec end;
    get_time(&end);
    uint64_t elapsed_microsecs = get_diff_time_microsec(&start, &end);

    printf("Elapsed: %lu ms\n", elapsed_microsecs / 1000);

    switch (res) {
        case Z3_L_FALSE:
            printf("Query is UNSAT%s\n", optimistic ? " [OPTIMISTIC]" : "");
            smt_solver.unsat_count += 1;
            smt_solver.unsat_time += elapsed_microsecs;
            break;
        case Z3_L_UNDEF:
            printf("Query is UNKNOWN%s\n", optimistic ? " [OPTIMISTIC]" : "");
            smt_solver.unknown_count += 1;
            smt_solver.unknown_time += elapsed_microsecs;
            break;
        case Z3_L_TRUE:
            printf("Query is SAT%s\n", optimistic ? " [OPTIMISTIC]" : "");
            smt_solver.sat_count += 1;
            smt_solver.sat_time += elapsed_microsecs;
            m = Z3_solver_get_model(smt_solver.ctx, solver);
            if (m) {
                Z3_model_inc_ref(smt_solver.ctx, m);
                smt_dump_solution(smt_solver.ctx, m, idx, optimistic ? 666 : 0);
            }
            qres = 1;
            break;
    }
    if (m)
        Z3_model_dec_ref(smt_solver.ctx, m);
    return qres;
}

static uintptr_t smt_query_eval_uint64(Z3_model m, Z3_ast e)
{
    uintptr_t value;
    Z3_ast    solution;
    Z3_bool   successfulEval =
        Z3_model_eval(smt_solver.ctx, m, e, Z3_TRUE, &solution);
    assert(successfulEval && "Failed to evaluate model");
    if (Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_NUMERAL_AST) {

#if Z3_VERSION <= 451
        Z3_bool successGet = Z3_get_numeral_int64(smt_solver.ctx, solution,
                                                  (long long int*)&value);
#else
        Z3_bool successGet =
            Z3_get_numeral_int64(smt_solver.ctx, solution, (int64_t*)&value);
#endif
        return value;
    } else {
        ABORT("Failed to evaluate using Z3 model.\n");
    }
}

static int smt_query_check_eval_uint64(Z3_solver solver, size_t idx, Z3_ast e,
                                       uintptr_t* value, uintptr_t dump_idx)
{
    int qres = 0;
#if 1
    struct timespec start;
    get_time(&start);

    Z3_model m   = NULL;
    Z3_lbool res = Z3_solver_check(smt_solver.ctx, solver);

    struct timespec end;
    get_time(&end);
    uint64_t elapsed_microsecs = get_diff_time_microsec(&start, &end);

    // printf("Elapsed: %lu ms\n", elapsed_microsecs / 1000);

    switch (res) {
        case Z3_L_FALSE:
            // printf("Query is UNSAT\n");
            smt_solver.unsat_count += 1;
            smt_solver.unsat_time += elapsed_microsecs;
            break;
        case Z3_L_UNDEF:
            // printf("Query is UNKNOWN\n");
            smt_solver.unknown_count += 1;
            smt_solver.unknown_time += elapsed_microsecs;
            break;
        case Z3_L_TRUE:
            // printf("Query is SAT\n");
            smt_solver.sat_count += 1;
            smt_solver.sat_time += elapsed_microsecs;
            m = Z3_solver_get_model(smt_solver.ctx, solver);
            if (m) {
                Z3_model_inc_ref(smt_solver.ctx, m);
                if (dump_idx) {
                    smt_dump_solution(smt_solver.ctx, m, idx, dump_idx);
                }
                if (value) {
                    *value = smt_query_eval_uint64(m, e);
                }
            }
            qres = 1;
            break;
    }
    if (m)
        Z3_model_dec_ref(smt_solver.ctx, m);
#endif
    return qres;
}

static void print_z3_ast_internal(Z3_ast e, uint8_t invert_op,
                                  uint8_t parent_is_concat)
{
#if 1 // disable concat parenting
    parent_is_concat = 0;
#endif
    Z3_context   ctx = smt_solver.ctx;
    Z3_app       app;
    Z3_func_decl decl;
    Z3_decl_kind decl_kind;
    unsigned     num_operands;

    const char* s_op          = NULL;
    uint8_t     op_is_boolean = 0;
    uint8_t     propagate_op  = 0;

    switch (Z3_get_ast_kind(ctx, e)) {

        case Z3_NUMERAL_AST: {
            Z3_sort  sort = Z3_get_sort(ctx, e);
            size_t   size = Z3_get_bv_sort_size(ctx, sort);
            uint64_t value;
            Z3_bool  r = Z3_get_numeral_uint64(ctx, e,
#if Z3_VERSION <= 451
                                              (long long unsigned int*)
#endif
                                              &value);
            if (r == Z3_TRUE) {
                printf("%lx#%lu", value, size);
            } else {
                const char* z3_query_str = Z3_ast_to_string(smt_solver.ctx, e);
                SAYF("%s", z3_query_str);
            }
            return;
        }

        case Z3_APP_AST: {

            app          = Z3_to_app(ctx, e);
            decl         = Z3_get_app_decl(ctx, app);
            decl_kind    = Z3_get_decl_kind(ctx, decl);
            num_operands = Z3_get_app_num_args(ctx, app);

            switch (decl_kind) {

                case Z3_OP_UNINTERPRETED: {
                    Z3_symbol symbol = Z3_get_decl_name(ctx, decl);
                    int       s      = Z3_get_symbol_int(ctx, symbol);
                    printf("input_%d", s);
                    return;
                }

                case Z3_OP_TRUE:
                    if (invert_op) {
                        printf("FALSE");
                    } else {
                        printf("TRUE");
                    }
                    return;
                case Z3_OP_FALSE:
                    if (invert_op) {
                        printf("TRUE");
                    } else {
                        printf("FALSE");
                    }
                    return;

                case Z3_OP_EQ: {
                    s_op = invert_op == 0 ? "==" : "!=";
                    break;
                }
                case Z3_OP_NOT: {
                    propagate_op = 1;
                    break;
                }
                case Z3_OP_SGEQ: {
                    s_op = invert_op == 0 ? ">=" : "<";
                    break;
                }
                case Z3_OP_SGT: {
                    s_op = invert_op == 0 ? ">" : "<=";
                    break;
                }
                case Z3_OP_SLEQ: {
                    s_op = invert_op == 0 ? "<=" : ">";
                    break;
                }
                case Z3_OP_SLT: {
                    s_op = invert_op == 0 ? "<" : ">=";
                    break;
                }
                case Z3_OP_UGEQ: {
                    s_op = invert_op == 0 ? ">=u" : "<u";
                    break;
                }
                case Z3_OP_UGT: {
                    s_op = invert_op == 0 ? ">u" : "<=u";
                    break;
                }
                case Z3_OP_ULEQ: {
                    s_op = invert_op == 0 ? "<=u" : ">u";
                    break;
                }
                case Z3_OP_ULT: {
                    s_op = invert_op == 0 ? "<u" : ">=u";
                    break;
                }

                case Z3_OP_CONCAT: {
                    assert(invert_op == 0);
                    s_op = "..";
                    break;
                }
                case Z3_OP_EXTRACT: {
                    assert(invert_op == 0);
                    break;
                }
                case Z3_OP_ZERO_EXT: {
                    assert(invert_op == 0);
                    break;
                }
                case Z3_OP_SIGN_EXT: {
                    assert(invert_op == 0);
                    break;
                }

                case Z3_OP_AND: {
                    s_op = "&&";
                    break;
                }

                case Z3_OP_OR: {
                    s_op = "||";
                    break;
                }

                case Z3_OP_BNOT: {
                    s_op = "~";
                    break;
                }
                case Z3_OP_BNEG: {
                    s_op = "-";
                    break;
                }

                case Z3_OP_BADD: {
                    s_op = "+";
                    break;
                }
                case Z3_OP_BSUB: {
                    s_op = "-";
                    break;
                }
                case Z3_OP_BMUL: {
                    s_op = "*";
                    break;
                }

                case Z3_OP_BUDIV: {
                    s_op = "/u";
                    break;
                }
                case Z3_OP_BUREM: {
                    s_op = "%u";
                    break;
                }
                case Z3_OP_BSDIV: {
                    s_op = "/";
                    break;
                }
                case Z3_OP_BSREM: {
                    s_op = "%";
                    break;
                }

                case Z3_OP_BSHL: {
                    s_op = "<<";
                    break;
                }
                case Z3_OP_BLSHR: {
                    s_op = ">>l";
                    break;
                }
                case Z3_OP_BASHR: {
                    s_op = ">>";
                    break;
                }

                case Z3_OP_BAND: {
                    s_op = "&";
                    break;
                }
                case Z3_OP_BOR: {
                    s_op = "|";
                    break;
                }
                case Z3_OP_BXOR: {
                    s_op = "^";
                    break;
                }

                case Z3_OP_ITE: {
                    break;
                }

                default: {
                    // printf("Unknown operator");
                    // return;
                }
            }
        }
    }

    if (num_operands == 1) {
        Z3_ast op1 = Z3_get_app_arg(ctx, app, 0);

        if (propagate_op && decl_kind == Z3_OP_NOT) {
            print_z3_ast_internal(op1, !invert_op, 0);
        } else {
            assert(propagate_op == 0);
            if (decl_kind == Z3_OP_EXTRACT) {

                int high = Z3_get_decl_int_parameter(ctx, decl, 0);
                int low  = Z3_get_decl_int_parameter(ctx, decl, 1);
                assert(low >= 0 && high >= low);

                printf("(");
                print_z3_ast_internal(op1, 0, 0);
                printf(")[%d:%d]", high, low);

            } else if (decl_kind == Z3_OP_SIGN_EXT) {

                int n = Z3_get_decl_int_parameter(ctx, decl, 0);
                assert(n > 0);

                printf("(");
                print_z3_ast_internal(op1, 0, 0);
                printf(" SExt %d)", n);

            } else if (decl_kind == Z3_OP_ZERO_EXT) {

                int n = Z3_get_decl_int_parameter(ctx, decl, 0);
                assert(n > 0);

                printf("(");
                print_z3_ast_internal(op1, 0, 0);
                printf(" ZExt %d)", n);

            } else if (decl_kind == Z3_OP_BNOT) {

                printf("%s", s_op);
                print_z3_ast_internal(op1, 0, 0);

            } else if (decl_kind == Z3_OP_AND) {

                print_z3_ast_internal(op1, 0, 0);

            } else if (decl_kind == Z3_OP_ROTATE_LEFT) {

                int n = Z3_get_decl_int_parameter(ctx, decl, 0);

                printf("ROL(");
                print_z3_ast_internal(op1, 0, 0);
                printf(", %d)", n);

            } else if (s_op) {

                assert(s_op);
                printf("%s", s_op);
                printf("(");
                print_z3_ast_internal(op1, 0, 0);
                printf(")");

            } else {
                print_z3_original(e);
                ABORT();
            }
        }

    } else if (num_operands == 2 && s_op) {
        Z3_ast op1 = Z3_get_app_arg(ctx, app, 0);
        Z3_ast op2 = Z3_get_app_arg(ctx, app, 1);

        if (!parent_is_concat || decl_kind != Z3_OP_CONCAT) {
            printf("(");
        }
        print_z3_ast_internal(op1, 0, decl_kind == Z3_OP_CONCAT);
        printf(" %s ", s_op);
        print_z3_ast_internal(op2, 0, decl_kind == Z3_OP_CONCAT);
        if (!parent_is_concat || decl_kind != Z3_OP_CONCAT) {
            printf(")");
        }

    } else if (num_operands == 3 && decl_kind == Z3_OP_ITE) {
        Z3_ast op1 = Z3_get_app_arg(ctx, app, 0);
        Z3_ast op2 = Z3_get_app_arg(ctx, app, 1);
        Z3_ast op3 = Z3_get_app_arg(ctx, app, 2);

        printf("ITE(");
        print_z3_ast_internal(op1, 0, 0);
        printf(", ");
        print_z3_ast_internal(op2, 0, 0);
        printf(", ");
        print_z3_ast_internal(op3, 0, 0);
        printf(")");

    } else {

        if (decl_kind == Z3_OP_AND || decl_kind == Z3_OP_OR ||
            decl_kind == Z3_OP_CONCAT) {
            // print_z3_original(e);
            printf("(");
            for (size_t i = 0; i < num_operands; i++) {
                print_z3_ast_internal(Z3_get_app_arg(ctx, app, i), 0, 0);
                if (i != num_operands - 1) {
                    printf(" %s ", s_op);
                }
            }
            printf(")");
        } else {
            printf("\nNumber of operands: %u - decl_kind: %x\n", num_operands,
                   decl_kind);
            print_z3_original(e);
            ABORT();
        }
    }
}

void print_z3_ast(Z3_ast e)
{
    // print_z3_original(e);
    // printf("\n");
    print_z3_ast_internal(e, 0, 0);
    printf("\n");
    // printf("\n");
}

void smt_print_ast_sort(Z3_ast e)
{
    Z3_sort sort = Z3_get_sort(smt_solver.ctx, e);
    printf("Sort: %s\n", Z3_sort_to_string(smt_solver.ctx, sort));
}

Z3_ast smt_bv_extract(Z3_ast e, size_t width)
{
    size_t high = (8 * width) - 1;
    size_t low  = 0;
    return Z3_mk_extract(smt_solver.ctx, high, low, e);
}

Z3_ast smt_to_bv_n(Z3_ast e, size_t width) // cast boolean to a bitvector
{
    if (Z3_get_sort_kind(smt_solver.ctx, Z3_get_sort(smt_solver.ctx, e)) ==
        Z3_BOOL_SORT) {
        e = Z3_mk_ite(smt_solver.ctx, e, smt_new_const(1, width * 8),
                      smt_new_const(0, width * 8));
        return optimize_z3_query(e);
    } else {
        return e;
    }
}

static inline uint8_t is_zero_const(Z3_ast e)
{
    Z3_context  ctx  = smt_solver.ctx;
    Z3_ast_kind kind = Z3_get_ast_kind(ctx, e);

    if (kind == Z3_NUMERAL_AST) {
        uint64_t value;
        Z3_bool  r = Z3_get_numeral_uint64(ctx, e,
#if Z3_VERSION <= 451
                                          (long long unsigned int*)
#endif
                                          &value);
        if (r == Z3_FALSE) {
            // result does not fit into 64 bits
            return 0;
        }
        return value == 0;
    }

    return 0;
}

static inline uint8_t is_const(Z3_ast e, uint64_t* value)
{
    Z3_context  ctx  = smt_solver.ctx;
    Z3_ast_kind kind = Z3_get_ast_kind(ctx, e);

    if (kind == Z3_NUMERAL_AST) {
        Z3_bool r = Z3_get_numeral_uint64(ctx, e,
#if Z3_VERSION <= 451
                                          (long long unsigned int*)
#endif
                                              value);
        if (r == Z3_FALSE) {
            // result does not fit into 64 bits
            return 0;
        }
        return 1;
    }

    return 0;
}

static inline Z3_decl_kind get_op(Z3_app app)
{
    Z3_func_decl decl = Z3_get_app_decl(smt_solver.ctx, app);
    return Z3_get_decl_kind(smt_solver.ctx, decl);
}

#define VERBOSE 0
void smt_bv_resize(Z3_ast* a, Z3_ast* b, ssize_t bytes_size)
{
#if VERBOSE
    printf("bytes_size=%ld\n", bytes_size);
#endif

    Z3_sort a_sort = Z3_get_sort(smt_solver.ctx, *a);
    Z3_sort b_sort = Z3_get_sort(smt_solver.ctx, *b);
    size_t  a_size;
    if (Z3_get_sort_kind(smt_solver.ctx, a_sort) == Z3_BOOL_SORT) {
        a_size = 1;
    } else {
        a_size = Z3_get_bv_sort_size(smt_solver.ctx, a_sort);
    }
    size_t b_size;
    if (Z3_get_sort_kind(smt_solver.ctx, b_sort) == Z3_BOOL_SORT) {
        b_size = 1;
    } else {
        b_size = Z3_get_bv_sort_size(smt_solver.ctx, b_sort);
    }
    if (a_size == b_size && (bytes_size == 0 || (bytes_size * 8) == a_size)) {
        return;
    }

    assert(bytes_size >= 0);

    size_t size;
    size_t base_index = 0;
    if (bytes_size < 0) {
        bytes_size = -bytes_size;
        base_index = bytes_size * 8;
        size       = bytes_size * 8;
    } else if (bytes_size == 0) {
        size = a_size > b_size ? a_size : b_size;
    } else {
        size = bytes_size * 8;
    }

#if VERBOSE
    printf("size=%ld a_size=%lu b_size=%lu base_index=%lu\n", size, a_size,
           b_size, base_index);
#endif

    if (Z3_get_sort_kind(smt_solver.ctx, a_sort) == Z3_BOOL_SORT) {
        *a = Z3_mk_ite(smt_solver.ctx, *a, smt_new_const(1, size),
                       smt_new_const(0, size));
    } else if (a_size > size) {
#if VERBOSE
        printf("EXTRACT in resize A\n");
        smt_print_ast_sort(*a);
#endif
        *a = Z3_mk_extract(smt_solver.ctx, size - 1 + base_index, base_index,
                           *a);
    } else if (a_size < size) {
#if VERBOSE
        printf("CONCAT in resize A: size_a=%lu size=%lu\n", a_size, size);
        smt_print_ast_sort(*a);
#endif
        if (OP(*a) == Z3_OP_CONCAT && is_zero_const(ARG1(*a))) {
            *a =
                Z3_mk_concat(smt_solver.ctx,
                             smt_new_const(0, size - SIZE(ARG2(*a))), ARG2(*a));
        } else {
            *a = Z3_mk_concat(smt_solver.ctx, smt_new_const(0, size - a_size),
                              *a);
        }
    }

    if (Z3_get_sort_kind(smt_solver.ctx, b_sort) == Z3_BOOL_SORT) {
        *b = Z3_mk_ite(smt_solver.ctx, *b, smt_new_const(1, size),
                       smt_new_const(0, size));
    } else if (b_size > size) {
#if VERBOSE
        printf("EXTRACT in resize B\n");
        smt_print_ast_sort(*b);
#endif
        *b = Z3_mk_extract(smt_solver.ctx, size - 1 + base_index, base_index,
                           *b);
    } else if (b_size < size) {
#if VERBOSE
        printf("CONCAT in resize B\n");
        smt_print_ast_sort(*b);
#endif
        if (OP(*b) == Z3_OP_CONCAT && is_zero_const(ARG1(*b))) {
            *b =
                Z3_mk_concat(smt_solver.ctx,
                             smt_new_const(0, size - SIZE(ARG2(*b))), ARG2(*b));
        } else {
            *b = Z3_mk_concat(smt_solver.ctx, smt_new_const(0, size - b_size),
                              *b);
        }
    }

#if VERBOSE
    printf("END smt_bv_resize\n");
    smt_print_ast_sort(*a);
    smt_print_ast_sort(*b);
#endif

    *a = optimize_z3_query(*a);
    *b = optimize_z3_query(*b);

#if VERBOSE
    printf("END smt_bv_resize\n");
    smt_print_ast_sort(*a);
    smt_print_ast_sort(*b);
#endif
}
#undef VERBOSE

Z3_ast smt_to_bv(Z3_ast e) { return smt_to_bv_n(e, 8); }

// ToDo: use a dictionary!
Expr*           expr_annotation_addr = NULL;
ExprAnnotation* expr_annotation;
void            add_expr_annotation(Expr* e, ExprAnnotation* ea)
{
    expr_annotation_addr = e;
    expr_annotation      = ea;
}

ExprAnnotation* get_expr_annotation(Expr* e)
{
    if (expr_annotation_addr == e) {
        return expr_annotation;
    } else {
        return NULL;
    }
}

typedef Z3_ast (*maker_op_t)(Z3_context, Z3_ast, Z3_ast);

static inline maker_op_t get_make_op(Z3_decl_kind decl_kind)
{
    switch (decl_kind) {
        case Z3_OP_EQ:
            return Z3_mk_eq;

        case Z3_OP_ULEQ:
            return Z3_mk_bvule;
        case Z3_OP_ULT:
            return Z3_mk_bvult;
        case Z3_OP_UGEQ:
            return Z3_mk_bvuge;
        case Z3_OP_UGT:
            return Z3_mk_bvugt;

        case Z3_OP_SLEQ:
            return Z3_mk_bvsle;
        case Z3_OP_SLT:
            return Z3_mk_bvslt;
        case Z3_OP_SGEQ:
            return Z3_mk_bvsge;
        case Z3_OP_SGT:
            return Z3_mk_bvsgt;

        case Z3_OP_BADD:
            return Z3_mk_bvadd;
        case Z3_OP_BSUB:
            return Z3_mk_bvsub;
        case Z3_OP_BMUL:
            return Z3_mk_bvmul;
        case Z3_OP_BUDIV:
            return Z3_mk_bvudiv;
        case Z3_OP_BSDIV:
            return Z3_mk_bvsdiv;
        case Z3_OP_BUREM:
            return Z3_mk_bvurem;
        case Z3_OP_BSREM:
            return Z3_mk_bvsrem;

        case Z3_OP_BAND:
            return Z3_mk_bvand;
        case Z3_OP_BOR:
            return Z3_mk_bvor;
        case Z3_OP_BXOR:
            return Z3_mk_bvxor;

        case Z3_OP_BSHL:
            return Z3_mk_bvshl;
        case Z3_OP_BLSHR:
            return Z3_mk_bvlshr;
        case Z3_OP_BASHR:
            return Z3_mk_bvashr;

        case Z3_OP_CONCAT:
            return Z3_mk_concat;

        default:
            printf("decl_kind %d not yet implemented\n", decl_kind);
            ABORT();
    }
}

#define SHIFT_OPT_MAX_BYTES 32

static inline uint8_t get_shifted_bytes(Z3_ast e, Z3_ast* bytes, int n)
{

    if (SIZE(e) / 8 > SHIFT_OPT_MAX_BYTES) {
        return 0;
    }

    if (OP(e) == Z3_OP_BSHL) {
        assert(N_ARGS(e) == 2);
        uint64_t value;
        if (!is_const(ARG2(e), &value) || OP(ARG1(e)) != Z3_OP_CONCAT) {
            // printf("Check SHL KO 1\n");
            return 0;
        }
        if ((value / 8) >= n || value % 8 != 0 || bytes[value / 8]) {
            // printf("Check SHL KO 2\n");
            return 0;
        }
        Z3_ast  bytes_concat[SHIFT_OPT_MAX_BYTES] = {0};
        uint8_t r = get_shifted_bytes(ARG1(e), bytes_concat, n);
        if (r) {
            Z3_ast byte       = NULL;
            int    byte_index = -1;
            for (size_t i = 0; i < 8; i++) {
                if (bytes_concat[i]) {
                    if (byte) {
                        // printf("Check SHL KO 3\n");
                        return 0;
                    } else {
                        byte       = bytes_concat[i];
                        byte_index = i;
                    }
                }
            }
            if (byte) {

                assert(byte_index >= 0);
                int new_index = byte_index - (value / 8);

                // printf("Found byte: ");
                // print_z3_ast(byte);
                // printf("\nbyte_index=%d new_index=%d value=%lu\n",
                //        byte_index, new_index, value);

                assert(new_index < n);
                if (!bytes[new_index]) {
                    bytes[new_index] = byte;
                }

                return 1;
            }
        }

        // printf("Check SHL KO 5\n");

    } else if (OP(e) == Z3_OP_CONCAT) {

        // printf("Check CONCAT\n");

        assert(N_ARGS(e) == 2);
        if (OP(ARG1(e)) == Z3_OP_CONCAT || OP(ARG1(e)) == Z3_OP_BSHL) {
            Z3_ast  bytes_1[SHIFT_OPT_MAX_BYTES] = {0};
            uint8_t r = get_shifted_bytes(ARG1(e), bytes_1, n);
            if (!r) {
                return 0;
            }
            for (size_t i = 0; i < 8; i++) {
                if (bytes[i]) {
                    // printf("Check CONCAT KO 9\n");
                    return 0;
                } else {
                    bytes[i] = bytes_1[i];
                }
            }
        } else if (is_zero_const(ARG1(e))) {
            // nothing to be done
        } else if (SIZE(ARG1(e)) == 8) {
            if (bytes[0]) {
                // printf("Check CONCAT KO 1\n");
                return 0;
            } else {
                bytes[0] = ARG1(e);
            }
        } else {
            // printf("Check CONCAT KO 2\n");
            return 0;
        }

        if (OP(ARG2(e)) == Z3_OP_CONCAT || OP(ARG2(e)) == Z3_OP_BSHL) {
            Z3_ast  bytes_1[SHIFT_OPT_MAX_BYTES] = {0};
            uint8_t r = get_shifted_bytes(ARG2(e), bytes_1, n);
            if (!r) {
                return 0;
            }
            for (size_t i = 0; i < 8; i++) {
                if (bytes_1[i]) {
                    if (bytes[(SIZE(ARG1(e)) / 8) + i]) {
                        // printf("Check CONCAT KO 7 %lu %ld\n", i,
                        //  (SIZE(ARG1(e)) / 8) + i);
                        return 0;
                    } else {
                        bytes[(SIZE(ARG1(e)) / 8) + i] = bytes_1[i];
                    }
                }
            }
        } else if (is_zero_const(ARG2(e))) {
            // nothing to be done
        } else if (SIZE(ARG2(e)) == 8) {
            if (bytes[SIZE(ARG1(e)) / 8]) {
                // printf("Check CONCAT KO 3\n");
                return 0;
            } else {
                bytes[SIZE(ARG1(e)) / 8] = ARG2(e);
            }
        } else {
            // printf("Check CONCAT KO 4: %u %u\n", OP(ARG2(e)), Z3_OP_BSHL);
            return 0;
        }

        // printf("Check CONCAT OK\n");
        return 1;

    } else if (OP(e) == Z3_OP_BOR || OP(e) == Z3_OP_BADD) {
        // printf("Check OR\n");
        assert(N_ARGS(e) == 2);
        uint8_t r1 = get_shifted_bytes(ARG1(e), bytes, n);
        uint8_t r2 = get_shifted_bytes(ARG2(e), bytes, n);
        // printf("Check OR %u %u\n", r1, r2);
        if (r1 && r2) {
            // printf("Check OR OK\n");
            return 1;
        }
    }

    // printf("Check CONCAT KO 5\n");
    return 0;
}

static int debug_translation = 0;
#if 0
uint64_t pattern_sdiv_64_675[] = { 'a', 64, 1066, 'a', 64, 1059, 'p', 127, 'p', 64, 'a', 128, 1030, 'a', 128, 1057, 'p', 64, 'a', 64, 1056,  'c', 0x0,'i', 'a', 128, 1057, 'p', 64,  'c', 0x1845c8a0ce512957, 'c', 0x6, };

typedef enum {
    UDIV,
    SDIV,
} pattern_type_t;

typedef struct {
    uint64_t* pattern;
    size_t pattern_size;
    pattern_type_t type;
    uint64_t value;
    size_t value_size;
} pattern_t;

pattern_t patterns[] = {
    {
        .pattern = pattern_sdiv_64_675,
        .pattern_size = sizeof(pattern_sdiv_64_675) / sizeof(uint64_t),
        .type = SDIV,
        .value = 675,
        .value_size = 64
    }
};

int match_pattern(Z3_ast e, uint64_t* pattern, int* pos, int len, Z3_ast* input) {

    if (*pos == len) return 1;

    uint64_t value;
    Z3_context  ctx  = smt_solver.ctx;
    Z3_ast_kind kind = Z3_get_ast_kind(ctx, e);

    // printf("Matching pattern at %d\n", *pos);
    // print_z3_ast(e);

    switch(pattern[*pos]) {

        case 'a': {
            if (len - *pos < 3) {
                // printf("Failed pattern at %d: not enough data\n", *pos);
                return 0;
            }
            *pos = *pos + 1;
            int size = IS_BOOL(e) ? 1 : SIZE(e);
            if (pattern[*pos] != size) {
                // printf("Failed pattern at %d: different size (expected=%lu, actual=%d)\n", *pos, pattern[*pos], size);
                return 0;
            }
            *pos = *pos + 1;
            Z3_decl_kind decl_kind = OP(e);
            if (pattern[*pos] != decl_kind) {
                // printf("Failed pattern at %d: different kind\n", *pos);
                return 0;
            }
            *pos = *pos + 1;
            int param_index = 0;
            while (pattern[*pos] == 'p') {
                if (PARAM(e, param_index) != pattern[*pos + 1]) {
                    // printf("Failed pattern at %d: different params\n", *pos);
                    return 0;
                }
                *pos = *pos + 2;
                param_index += 1;
            }
            unsigned num_operands = N_ARGS(e);
            for (size_t i = 0; i < num_operands; i++) {
                int r = match_pattern(ARG(e, i), pattern, pos, len, input);
                if (!r) {
                    return 0;
                }
            }
            return 1;
            break;
        }

        case 'c': {
            if (len - *pos < 2) {
                return 0;
            }
            if (is_const(e, &value) && value == pattern[*pos+1]) {
                *pos = *pos + 2;
                return 1;
            } else {
                return 0;
            }
        }

        case 'i': {
            *pos = *pos + 1;
            *input = e;
            return 1;
            break;
        }

        default:
            return 0;
    }

    return 0;
}
#endif
#if 0
Z3_ast optimize_z3_query_division(Z3_ast e)
{
#if 0
    printf("\nTransformation on: ");
    print_z3_ast_internal(e, 0, 0);
    printf("\n");
#endif

    Z3_context  ctx  = smt_solver.ctx;

    for (size_t i = 0; i < sizeof(patterns) / sizeof(pattern_t); i++) {
        Z3_ast pattern_input = NULL;
        int pos = 0, len = patterns[i].pattern_size;
        if (match_pattern(e, patterns[i].pattern, &pos, len, &pattern_input)
                && pos == len && pattern_input) {
            if (patterns[i].type == SDIV) {
                size_t original_size = SIZE(e);
                if (SIZE(pattern_input) < patterns[i].value_size) {
                    pattern_input = Z3_mk_concat(ctx, smt_new_const(0, patterns[i].value_size - SIZE(pattern_input)), pattern_input);
                }
                e = Z3_mk_bvsdiv(ctx, pattern_input, smt_new_const(patterns[i].value, patterns[i].value_size));
                if (SIZE(e) < original_size) {
                    e = Z3_mk_concat(ctx, smt_new_const(0, original_size - SIZE(e)), e);
                }
                ABORT();
                return e;
            }
            ABORT();
        }
    }

    Z3_ast_kind kind = Z3_get_ast_kind(ctx, e);
    if (kind != Z3_APP_AST) {
        return e;
    }

    uint64_t value;
    Z3_decl_kind decl_kind    = OP(e);
    if (decl_kind == Z3_OP_CONCAT
            && is_const(ARG1(e), &value)
            && value == 0) {

        // 32 bit unsigned division by 3
        if (OP(ARG2(e)) == Z3_OP_EXTRACT
                && PARAM1(ARG2(e)) == 63 && PARAM2(ARG2(e)) == 33
                && OP(ARG1(ARG2(e))) == Z3_OP_BMUL
                && is_const(ARG1(ARG1(ARG2(e))), &value)
                && value == 0xaaaaaaab
                && OP(ARG2(ARG1(ARG2(e)))) == Z3_OP_CONCAT) {

            Z3_ast a = ARG2(ARG2(ARG1(ARG2(e))));
            Z3_ast b = smt_new_const(3, 32);
            e = Z3_mk_bvudiv(ctx, a, b);
            e = Z3_mk_concat(ctx, smt_new_const(0, 32), e);
            // print_z3_ast(e);
            return e;
        }

        // 32 bit unsigned division by 5
        if (OP(ARG2(e)) == Z3_OP_EXTRACT
                && PARAM1(ARG2(e)) == 63 && PARAM2(ARG2(e)) == 34
                && OP(ARG1(ARG2(e))) == Z3_OP_BMUL
                && is_const(ARG1(ARG1(ARG2(e))), &value)
                && value == 0xcccccccd
                && OP(ARG2(ARG1(ARG2(e)))) == Z3_OP_CONCAT) {

            Z3_ast a = ARG2(ARG2(ARG1(ARG2(e))));
            Z3_ast b = smt_new_const(5, 32);
            e = Z3_mk_bvudiv(ctx, a, b);
            e = Z3_mk_concat(ctx, smt_new_const(0, 32), e);
            // print_z3_ast(e);
            return e;
        }

        // 64 bit unsigned division by 3
        if (SIZE(ARG1(e)) == 1
                && OP(ARG2(e)) == Z3_OP_EXTRACT
                && PARAM1(ARG2(e)) == 127 && PARAM2(ARG2(e)) == 65
                && OP(ARG1(ARG2(e))) == Z3_OP_BMUL
                && OP(ARG2(ARG1(ARG2(e)))) == Z3_OP_CONCAT
                && is_const(ARG2(ARG2(ARG1(ARG2(e)))), &value)
                && value == 0xaaaaaaaaaaaaaaab
                && is_zero_const(ARG1(ARG2(ARG1(ARG2(e)))))
                && OP(ARG1(ARG1(ARG2(e)))) == Z3_OP_CONCAT
                && is_zero_const(ARG1(ARG1(ARG1(ARG2(e)))))
                ) {

            Z3_ast a = ARG2(ARG1(ARG1(ARG2(e))));
            if (SIZE(a) < 64) {
                a = Z3_mk_concat(ctx, smt_new_const(0, 64 - SIZE(a)), a);
            }
            Z3_ast b = smt_new_const(3, 64);
            e = Z3_mk_bvudiv(ctx, a, b);
            // print_z3_ast(e);
            return e;
        }

        // 64 bit unsigned division by 5
        if (SIZE(ARG1(e)) == 2
                && OP(ARG2(e)) == Z3_OP_EXTRACT
                && PARAM1(ARG2(e)) == 127 && PARAM2(ARG2(e)) == 66
                && OP(ARG1(ARG2(e))) == Z3_OP_BMUL
                && OP(ARG2(ARG1(ARG2(e)))) == Z3_OP_CONCAT
                && is_const(ARG2(ARG2(ARG1(ARG2(e)))), &value)
                && value == 0xcccccccccccccccd
                && is_zero_const(ARG1(ARG2(ARG1(ARG2(e)))))
                && OP(ARG1(ARG1(ARG2(e)))) == Z3_OP_CONCAT
                && is_zero_const(ARG1(ARG1(ARG1(ARG2(e)))))
                ) {

            Z3_ast a = ARG2(ARG1(ARG1(ARG2(e))));
            if (SIZE(a) < 64) {
                a = Z3_mk_concat(ctx, smt_new_const(0, 64 - SIZE(a)), a);
            }
            Z3_ast b = smt_new_const(5, 64);
            e = Z3_mk_bvudiv(ctx, a, b);
            // print_z3_ast(e);
            return e;
        }

    } else if (decl_kind == Z3_OP_BSUB) {

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        // 32 bit integer division by 3
        if (SIZE(e) == 32
                && OP(op1) == Z3_OP_EXTRACT
                && OP(ARG1(op1)) == Z3_OP_BMUL
                && OP(ARG2(ARG1(op1))) == Z3_OP_SIGN_EXT
                && OP(op2) == Z3_OP_EXTRACT
                && OP(ARG1(op2)) == Z3_OP_BASHR
                && is_const(ARG2(ARG1(op2)), &value)
                && value == 31) {

            uint64_t div_consts[] = {
                0x55555556,
            };

            uint64_t div_values[] = {
                3,
            };

            for (size_t i = 0; i < sizeof(div_consts) / sizeof(div_values); i++) {
                if (is_const(ARG1(ARG1(op1)), &value)
                        && value == div_consts[i]) {
                    print_z3_ast(e);
                    Z3_ast a = ARG1(ARG2(ARG1(op1)));
                    Z3_ast b = smt_new_const(div_values[i], 32);
                    e = Z3_mk_bvsdiv(ctx, a, b);
                    // print_z3_ast(e);
                    return e;
                }
            }
        }

        // 32 bit integer division by 5
        if (SIZE(e) == 32
                && OP(op1) == Z3_OP_EXTRACT
                && OP(ARG1(op1)) == Z3_OP_BASHR
                && OP(ARG1(ARG1(op1))) == Z3_OP_SIGN_EXT
                && OP(ARG1(ARG1(ARG1(op1)))) == Z3_OP_EXTRACT
                && OP(ARG1(ARG1(ARG1(ARG1(op1))))) == Z3_OP_BMUL
                && OP(ARG2(ARG1(ARG1(ARG1(ARG1(op1)))))) == Z3_OP_SIGN_EXT
                && OP(op2) == Z3_OP_EXTRACT
                && OP(ARG1(op2)) == Z3_OP_BASHR
                && is_const(ARG2(ARG1(op2)), &value)
                && value == 31
                ) {

            uint64_t div_consts[] = {
                0x66666667,
            };

            uint64_t div_values[] = {
                5,
            };

            for (size_t i = 0; i < sizeof(div_consts) / sizeof(div_values); i++) {
                if (is_const(ARG1(ARG1(ARG1(ARG1(ARG1(op1))))), &value)
                        && value == div_consts[i]) {
                    Z3_ast a = ARG1(ARG2(ARG1(ARG1(ARG1(ARG1(op1))))));
                    Z3_ast b = smt_new_const(div_values[i], 32);
                    e = Z3_mk_bvsdiv(ctx, a, b);
                    // print_z3_ast(e);
                    return e;
                }
            }
        }

    } else if (decl_kind == Z3_OP_EXTRACT) {

        Z3_ast op1 = ARG1(e);

        // 64 bit signed division by 3
        if (PARAM1(e) == 127 && PARAM2(e) == 64
                && OP(ARG1(e)) == Z3_OP_BMUL
                && OP(ARG2(ARG1(e))) == Z3_OP_SIGN_EXT
                && is_const(ARG1(ARG2(ARG1(e))), &value)
                && value == 0x5555555555555556
                ) {

            Z3_ast a = ARG1(ARG1(ARG1(e)));
            Z3_ast b = smt_new_const(3, 64);
            e = Z3_mk_bvsdiv(ctx, a, b);
            // print_z3_ast(e);
            return e;
        }

    } else if (decl_kind == Z3_OP_BASHR) {

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        // 64 bit signed division by 5
        if (is_const(op2, &value) 
                && value == 1
                && OP(op1) == Z3_OP_EXTRACT
                && PARAM1(op1) == 127
                && PARAM2(op1) == 64
                && OP(ARG1(op1)) == Z3_OP_BMUL
                && OP(ARG2(ARG1(op1))) == Z3_OP_SIGN_EXT
                && is_const(ARG1(ARG2(ARG1(op1))), &value)
                && value == 0x6666666666666667
                ) {

            Z3_ast a = ARG1(ARG1(ARG1(op1)));
            Z3_ast b = smt_new_const(5, 64);
            e = Z3_mk_bvsdiv(ctx, a, b);
            // print_z3_ast(e);
            return e;
        }

    }

    return e;
}
#endif

Z3_ast optimize_z3_query(Z3_ast e)
{
#if 0
    //if (debug_translation) {
    printf("\nTransformation on: ");
    print_z3_ast_internal(e, 0, 0);
    printf("\n");
    //}
#endif

    Z3_context  ctx  = smt_solver.ctx;
    Z3_ast_kind kind = Z3_get_ast_kind(ctx, e);
    if (kind != Z3_APP_AST) {
        return e;
    }

    Z3_decl_kind decl_kind    = OP(e);
    unsigned     num_operands = N_ARGS(e);

    uint64_t value, value2;

    // constant folding
    if (OP(e) != Z3_OP_UNINTERPRETED && (IS_BOOL(e) || SIZE(e) <= 64)) {
        uint8_t is_constant = 1;
        for (size_t i = 0; i < num_operands; i++) {
            Z3_ast child = Z3_get_app_arg(ctx, APP(e), i);
            if (!is_const(child, &value)) {
                is_constant = 0;
                break;
            }
        }
        if (is_constant) {
            // printf("CONSTANT PROPAGATION: ");
            // print_z3_ast(e);
            value = Z3_custom_eval(ctx, e, NULL, NULL, 0);
            if (!IS_BOOL(e)) {
                e = smt_new_const(value, SIZE(e));
            } else {
                e = value ? Z3_mk_true(ctx) : Z3_mk_false(ctx);
            }
            // printf("CONSTANT PROPAGATION DONE: ");
            // print_z3_ast(e);
            return e;
        }
    }
    if (OP(e) != Z3_OP_UNINTERPRETED) {
        uint8_t is_constant = 1;
        for (size_t i = 0; i < num_operands; i++) {
            Z3_ast      child = Z3_get_app_arg(ctx, APP(e), i);
            Z3_ast_kind kind  = Z3_get_ast_kind(ctx, e);
            if (kind != Z3_NUMERAL_AST) {
                is_constant = 0;
                break;
            }
        }
        if (is_constant) {
            // if we are here this means that SIZE(e) > 64
            // printf("CONSTANT PROPAGATION: ");
            // print_z3_ast(e);
            e = Z3_simplify(smt_solver.ctx, e);
            // printf("CONSTANT PROPAGATION DONE: ");
            // print_z3_ast(e);
            return e;
        }
    }

    if (decl_kind == Z3_OP_NOT) {
        Z3_ast op1          = ARG1(e);
        Z3_ast op1_original = op1;
        op1                 = optimize_z3_query(op1);
        if (op1_original != op1) {
            e = Z3_mk_not(ctx, op1);
        }
        return e;
    }

    // if (decl_kind == Z3_OP_EXTRACT)
    // printf("\ndecl_kind: %u %u\n", decl_kind, Z3_OP_EQ);

    if (decl_kind == Z3_OP_EQ ||
        (decl_kind >= Z3_OP_ULEQ && decl_kind <= Z3_OP_SGT)) {

        assert(num_operands == 2);

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        // from:
        //  X - Y op 0
        // whereL
        //  op is a comparison operator
        // to:
        //  X == Y
        if (is_zero_const(op1) && OP(op2) == Z3_OP_BSUB) {
            e = get_make_op(decl_kind)(ctx, ARG2(op2), ARG1(op2));
            return optimize_z3_query(e);
        } else if (is_zero_const(op2) && OP(op1) == Z3_OP_BSUB) {
            e = get_make_op(decl_kind)(ctx, ARG1(op1), ARG2(op1));
            return optimize_z3_query(e);
        }

        // from:
        //  (0x0#N .. X#M) op C#(N+M)
        // where:
        //  - op is an unsigned comparison op
        //  - C <= MASK_FF(M)
        // to:
        //  X op C#size(X)
        if ((decl_kind == Z3_OP_EQ || decl_kind == Z3_OP_ULEQ ||
             decl_kind == Z3_OP_UGEQ || decl_kind == Z3_OP_ULT ||
             decl_kind == Z3_OP_UGT) &&
            OP(op1) == Z3_OP_CONCAT && is_const(op2, &value) &&
            value <= FF_MASK(SIZE(ARG2(op1))) && is_zero_const(ARG1(op1))) {

            op2 = smt_new_const(value, SIZE(ARG2(op1)));
            e   = get_make_op(decl_kind)(ctx, ARG2(op1), op2);
            return optimize_z3_query(e);
        }
        if ((decl_kind == Z3_OP_EQ || decl_kind == Z3_OP_ULEQ ||
             decl_kind == Z3_OP_UGEQ || decl_kind == Z3_OP_ULT ||
             decl_kind == Z3_OP_UGT) &&
            OP(op2) == Z3_OP_CONCAT && is_const(op1, &value) &&
            value <= FF_MASK(SIZE(ARG2(op2))) && is_zero_const(ARG1(op2))) {

            op1 = smt_new_const(value, SIZE(ARG2(op2)));
            e   = get_make_op(decl_kind)(ctx, op1, ARG2(op2));
            return optimize_z3_query(e);
        }

        // from:
        //   ((0#M .. X) - C#N)[high:0] == 0
        // where:
        //   - C <= (1 << high + 1) - 1
        // to:
        //   X == C#size(X)
        if (decl_kind == Z3_OP_EQ && is_zero_const(op2) &&
            OP(op1) == Z3_OP_EXTRACT) {

            int high = PARAM1(op1);
            int low  = PARAM2(op1);
            assert(low >= 0 && high >= low);

            if (low == 0 && OP(ARG1(op1)) == Z3_OP_BSUB &&
                N_ARGS(ARG1(op1)) == 2 && is_const(ARG2(ARG1(op1)), &value) &&
                value <= FF_MASK(high + 1) &&
                OP(ARG1(ARG1(op1))) == Z3_OP_CONCAT &&
                N_ARGS(ARG1(ARG1(op1))) == 2 &&
                is_zero_const(ARG1(ARG1(ARG1(op1))))) {

                op2 = smt_new_const(value, SIZE(ARG2(ARG1(ARG1(op1)))));
                op1 = ARG2(ARG1(ARG1(op1)));
                e   = Z3_mk_eq(ctx, op1, op2);
                return optimize_z3_query(e);
            }
        }

        // from:
        //   (0#M .. X)[high:0] op Y
        // where:
        //   - size(X) == high + 1
        // to:
        //   X op Y
        if (OP(op1) == Z3_OP_EXTRACT && OP(ARG1(op1)) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG1(op1)))) {

            int high = PARAM1(op1);
            int low  = PARAM2(op1);
            assert(low >= 0 && high >= low);

            if (low == 0 && SIZE(ARG2(ARG1(op1))) == high + 1) {
                op1 = ARG2(ARG1(op1));
                e   = get_make_op(decl_kind)(ctx, op1, op2);
                return optimize_z3_query(e);
            }
        }

        // from:
        //   if (X) { 0#N } else { C#N } == 0#N
        // to:
        //   X
        // from:
        //   if (X) { C#N } else { 0#N } == 0#N
        // to:
        //   !X
        uint64_t value2;
        if (decl_kind == Z3_OP_EQ && OP(op1) == Z3_OP_ITE &&
            is_zero_const(op2) && is_const(ARG2(op1), &value) &&
            is_const(ARG3(op1), &value2)) {

            if (value == 0 && value2 != 0) {
                e = ARG1(op1);
                return e;
            }

            if (value != 0 && value2 == 0) {
                e = Z3_mk_not(ctx, ARG1(op1));
                return e;
            }
        }

        // from:
        //  (0x0#N .. X#M) == (0x0#N .. Y#M)
        // to:
        //  X == Y
        if ((decl_kind == Z3_OP_EQ || decl_kind == Z3_OP_ULEQ ||
             decl_kind == Z3_OP_UGEQ || decl_kind == Z3_OP_ULT ||
             decl_kind == Z3_OP_UGT) &&
            OP(op1) == Z3_OP_CONCAT && OP(op2) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(op1)) && is_zero_const(ARG1(op2)) &&
            SIZE(ARG1(op1)) == SIZE(ARG1(op2))) {

            e = get_make_op(decl_kind)(ctx, ARG2(op1), ARG2(op2));
            return optimize_z3_query(e);
        }

        // from:
        //  ((0x0#N .. X#M) - (0x0#N .. Y#M))[high:0] op 0
        // where:
        //  - op is an unsigned comparison operator
        //  - M == high + 1
        // to:
        //  X == Y
        if ((decl_kind == Z3_OP_EQ || decl_kind == Z3_OP_ULEQ ||
             decl_kind == Z3_OP_UGEQ || decl_kind == Z3_OP_ULT ||
             decl_kind == Z3_OP_UGT) &&
            OP(op1) == Z3_OP_EXTRACT && is_zero_const(op2) &&
            OP(ARG1(op1)) == Z3_OP_BSUB &&
            OP(ARG1(ARG1(op1))) == Z3_OP_CONCAT &&
            OP(ARG2(ARG1(op1))) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG1(ARG1(op1)))) &&
            is_zero_const(ARG1(ARG2(ARG1(op1))))) {

            int high = PARAM1(op1);
            int low  = PARAM2(op1);

            if (low == 0 && high + 1 == SIZE(ARG2(ARG1(ARG1(op1)))) &&
                high + 1 == SIZE(ARG2(ARG2(ARG1(op1))))) {

                e = get_make_op(decl_kind)(ctx, ARG2(ARG1(ARG1(op1))),
                                           ARG2(ARG2(ARG1(op1))));
                return optimize_z3_query(e);
            }
        }

        // from:
        //  C1 op ((0 .. X) >>l C2)
        // where:
        //  - op is an unsigned comparison operator
        //  - C1 < FF_MASK(SIZE(X))
        //  - C2 < FF_MASK(SIZE(X))
        // to:
        //  C1 op X >>l C2
        if ((decl_kind == Z3_OP_EQ || decl_kind == Z3_OP_ULEQ ||
             decl_kind == Z3_OP_UGEQ || decl_kind == Z3_OP_ULT ||
             decl_kind == Z3_OP_UGT) &&
            is_const(op1, &value) && OP(op2) == Z3_OP_BLSHR &&
            OP(ARG1(op2)) == Z3_OP_CONCAT && is_zero_const(ARG1(ARG1(op2))) &&
            value < FF_MASK(SIZE(ARG2(ARG1(op2)))) &&
            is_const(ARG2(op2), &value2) &&
            value2 < FF_MASK(SIZE(ARG2(ARG1(op2))))) {

            Z3_ast c1 = smt_new_const(value, SIZE(ARG2(ARG1(op2))));
            Z3_ast c2 = smt_new_const(value2, SIZE(ARG2(ARG1(op2))));
            e         = Z3_mk_bvlshr(ctx, ARG2(ARG1(op2)), c2);
            e         = get_make_op(decl_kind)(ctx, c1, e);
            return optimize_z3_query(e);
        }

        if (OP(op1) == Z3_OP_EXTRACT) {
            return get_make_op(decl_kind)(ctx, optimize_z3_query(op1), op2);
        }

        if (OP(op2) == Z3_OP_EXTRACT) {
            return get_make_op(decl_kind)(ctx, op1, optimize_z3_query(op2));
        }

        // from:
        //  (X + C1#N) == C2#N
        // to:
        //  X == (C2 - C1)#N
        if (OP(e) == Z3_OP_EQ && OP(op1) == Z3_OP_BADD && N_ARGS(op1) == 2 &&
            is_const(ARG2(op1), &value) && is_const(op2, &value2)) {

            Z3_ast c = smt_new_const(value2 - value, SIZE(op2));
            return get_make_op(decl_kind)(ctx, ARG1(op1), c);
        }

        // from:
        //  (X - C1#N) == C2#N
        // to:
        //  X == (C2 + C1)#N
        if (OP(e) == Z3_OP_EQ && OP(op1) == Z3_OP_BSUB && N_ARGS(op1) == 2 &&
            is_const(ARG2(op1), &value) && is_const(op2, &value2)) {

            Z3_ast c = smt_new_const(value2 + value, SIZE(op2));
            return get_make_op(decl_kind)(ctx, ARG1(op1), c);
        }

    } else if (decl_kind == Z3_OP_EXTRACT) {

        Z3_ast op1  = ARG1(e);
        int    high = PARAM1(e);
        int    low  = PARAM2(e);

        uint64_t value2;

        if (low == 0 && SIZE(op1) == high + 1) {
            return op1;
        }

        if (low == 0 && is_const(op1, &value)) {
            return smt_new_const(value, high + 1);
        }

        if (low == high && is_const(op1, &value)) {
            return smt_new_const(value >> low, 1);
        }

        if (OP(op1) == Z3_OP_CONCAT && N_ARGS(op1) == 2) {

            // printf("EXTRACT OPT\n");

            // keep only ARG2
            if (high < SIZE(ARG2(op1))) {
                // printf("EXTRACT OPT A\n");
                e = Z3_mk_extract(ctx, high, low, ARG2(op1));
                return optimize_z3_query(e);
            }

            // keep only ARG1
            if (low >= SIZE(ARG2(op1))) {
                // printf("EXTRACT OPT B\n");
                e = Z3_mk_extract(ctx, high - SIZE(ARG2(op1)),
                                  low - SIZE(ARG2(op1)), ARG1(op1));
                return optimize_z3_query(e);
            }

            // keep both but propagate extract

            // printf("EXTRACT OPT C\n");

            Z3_ast a = Z3_mk_extract(ctx, high - SIZE(ARG2(op1)), 0, ARG1(op1));

            Z3_ast b = Z3_mk_extract(ctx, SIZE(ARG2(op1)) - 1, low, ARG2(op1));

            a = optimize_z3_query(a);
            b = optimize_z3_query(b);

            e = Z3_mk_concat(ctx, a, b);
            return optimize_z3_query(e);
        }

        if (OP(op1) == Z3_OP_EXTRACT) {

            // printf("EXTRACT OPT D\n");

            unsigned nested_high = PARAM1(op1);
            unsigned nested_low  = PARAM2(op1);

            size_t orig_size = SIZE(e);

            e = Z3_mk_extract(ctx, high + nested_low, low + nested_low,
                              ARG1(op1));

            return optimize_z3_query(e);
        }

        if (OP(op1) == Z3_OP_BOR && N_ARGS(op1) == 2) {

            // printf("EXTRACT OPT E\n");

            Z3_ast a = Z3_mk_extract(ctx, high, low, ARG1(op1));
            a        = optimize_z3_query(a);
            Z3_ast b = Z3_mk_extract(ctx, high, low, ARG2(op1));
            b        = optimize_z3_query(b);
            e        = Z3_mk_bvor(ctx, a, b);
            return optimize_z3_query(e);
        }

        if (OP(op1) == Z3_OP_BAND && N_ARGS(op1) == 2) {

            // printf("EXTRACT OPT F\n");

            Z3_ast a = Z3_mk_extract(ctx, high, low, ARG1(op1));
            a        = optimize_z3_query(a);
            Z3_ast b = Z3_mk_extract(ctx, high, low, ARG2(op1));
            b        = optimize_z3_query(b);
            e        = Z3_mk_bvand(ctx, a, b);
            return optimize_z3_query(e);
        }

        // from:
        //  (Y .. X)[bit:bit]
        // to:
        //  X[bit:bit] iff bit < size(X)
        //  Y[bit - size(X) : bit - size(X)] iff b >= size(X)
        if (OP(op1) == Z3_OP_CONCAT && high == low) {
            if (low < SIZE(ARG2(op1))) {
                e = Z3_mk_extract(ctx, low, low, ARG2(op1));
                return optimize_z3_query(e);
            } else {
                e = Z3_mk_extract(ctx, low - SIZE(ARG2(op1)),
                                  low - SIZE(ARG2(op1)), ARG1(op1));
                return optimize_z3_query(e);
            }
        }

        // from:
        //   (if (X) { C1#N } else { C2#N })[high:0]
        // where:
        //   C <= FF_MASK(high + 1)
        // to:
        //   if (X) { C1#(high + 1) } else { C2#(high + 1) }
        if (OP(op1) == Z3_OP_ITE && low == 0 && is_const(ARG2(op1), &value) &&
            is_const(ARG3(op1), &value2) && value <= FF_MASK(high + 1) &&
            value2 <= FF_MASK(high + 1)) {

            Z3_ast c1 = smt_new_const(value, high + 1);
            Z3_ast c2 = smt_new_const(value2, high + 1);
            e         = Z3_mk_ite(ctx, ARG1(op1), c1, c2);
            return optimize_z3_query(e);
        }

        // from:
        //   (0#M .. X)[high:0]))
        // where:
        //   - size(X) == high + 1
        // to:
        //   X
        if (OP(op1) == Z3_OP_CONCAT && is_zero_const(ARG1(op1))) {

            // printf("EXTRACT OPT E\n");

            if (low == 0 && SIZE(ARG2(op1)) <= high + 1) {
                if (SIZE(ARG2(op1)) == high + 1) {
                    e = ARG2(op1);
                } else {
                    Z3_ast z = smt_new_const(0, (high + 1) - SIZE(ARG2(op1)));
                    e        = Z3_mk_concat(ctx, z, ARG2(op1));
                }
                return optimize_z3_query(e);
            }
        }

        // from:
        //   ((0#M .. X) - C#N)[high:0]))
        // where:
        //   - C < MASK_FF(SIZE(X))
        //   - size(X) == high + 1
        // to:
        //   X - C#size(X)
        if (low == 0 && OP(op1) == Z3_OP_BSUB &&
            OP(ARG1(op1)) == Z3_OP_CONCAT && is_zero_const(ARG1(ARG1(op1))) &&
            is_const(ARG2(op1), &value) &&
            value < FF_MASK(SIZE(ARG2(ARG1(op1))))) {

            if (SIZE(ARG2(ARG1(op1))) == high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvsub(ctx, ARG2(ARG1(op1)), c);
                return optimize_z3_query(e);
            }
        }
        // symmetric
        if (low == 0 && OP(op1) == Z3_OP_BSUB &&
            OP(ARG2(op1)) == Z3_OP_CONCAT && is_zero_const(ARG1(ARG2(op1))) &&
            is_const(ARG1(op1), &value) &&
            value < FF_MASK(SIZE(ARG2(ARG2(op1))))) {

            if (SIZE(ARG2(ARG2(op1))) == high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvsub(ctx, c, ARG2(ARG2(op1)));
                return optimize_z3_query(e);
            }
        }
        // same but with addition
        if (low == 0 && OP(op1) == Z3_OP_BADD &&
            OP(ARG1(op1)) == Z3_OP_CONCAT && is_zero_const(ARG1(ARG1(op1))) &&
            is_const(ARG2(op1), &value) &&
            value < FF_MASK(SIZE(ARG2(ARG1(op1))))) {

            if (SIZE(ARG2(ARG1(op1))) == high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvadd(ctx, ARG2(ARG1(op1)), c);
                return optimize_z3_query(e);
            }
        }
        // symmetric with addition
        if (low == 0 && OP(op1) == Z3_OP_BADD &&
            OP(ARG2(op1)) == Z3_OP_CONCAT && is_zero_const(ARG1(ARG2(op1))) &&
            is_const(ARG1(op1), &value) &&
            value < FF_MASK(SIZE(ARG2(ARG2(op1))))) {

            if (SIZE(ARG2(ARG2(op1))) == high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvadd(ctx, c, ARG2(ARG2(op1)));
                return optimize_z3_query(e);
            }
        }

        // from:
        //   ((0#M1 .. X) op (0#M2 .. Y))[high:0]))
        // where:
        //   - size(X) <= high + 1
        //   - size(Y) <= high + 1
        // to:
        //   ((0#K1 .. X) op (0#K2 .. Y))
        // where:
        //   K1 = high + 1 - size(X)
        //   K2 = high + 1 - size(Y)
        if (low == 0 && N_ARGS(op1) == 2 && OP(op1) != Z3_OP_CONCAT &&
            OP(op1) != Z3_OP_EXTRACT &&
            //
            ((OP(ARG1(op1)) == Z3_OP_CONCAT && N_ARGS(ARG1(op1)) == 2 &&
              is_zero_const(ARG1(ARG1(op1))) &&
              SIZE(ARG2(ARG1(op1))) <= high + 1) ||
             (is_const(ARG1(op1), &value) && value <= FF_MASK(high + 1)))
            //
            &&
            //
            ((OP(ARG2(op1)) == Z3_OP_CONCAT && N_ARGS(ARG2(op1)) == 2 &&
              is_zero_const(ARG1(ARG2(op1))) &&
              SIZE(ARG2(ARG2(op1))) <= high + 1) ||
             (is_const(ARG2(op1), &value2) && value2 <= FF_MASK(high + 1)))) {

            Z3_ast a =
                is_const(ARG1(op1), &value) ? ARG1(op1) : ARG2(ARG1(op1));

            Z3_ast b =
                is_const(ARG2(op1), &value2) ? ARG2(op1) : ARG2(ARG2(op1));

            if (SIZE(a) < high + 1) {
                Z3_ast c = smt_new_const(0, high + 1 - SIZE(a));
                a        = Z3_mk_concat(ctx, c, a);
            } else if (SIZE(a) > high + 1) {
                // this is a const
                a = smt_new_const(value & FF_MASK(high + 1), high + 1);
            }
            if (SIZE(b) < high + 1) {
                b = Z3_mk_concat(ctx, smt_new_const(0, high + 1 - SIZE(b)), b);
            } else if (SIZE(b) > high + 1) {
                // this is a const
                b = smt_new_const(value2 & FF_MASK(high + 1), high + 1);
            }
            e = get_make_op(OP(op1))(ctx, a, b);
            e = optimize_z3_query(e);
            return e;
        }

        if (OP(op1) == Z3_OP_BSDIV && OP(ARG1(op1)) == Z3_OP_SIGN_EXT &&
            OP(ARG2(op1)) == Z3_OP_CONCAT && is_zero_const(ARG1(ARG2(op1))) &&
            high < PARAM1(ARG1(op1))) {

            unsigned n_signed = PARAM1(ARG1(op1));
            unsigned n_zero   = SIZE(ARG1(ARG2(op1)));
            if (n_zero > n_signed) {
                Z3_ast a = ARG1(ARG1(op1));
                Z3_ast z = smt_new_const(0, n_zero - n_signed);
                Z3_ast b = Z3_mk_concat(ctx, z, ARG2(ARG2(op1)));
                e        = Z3_mk_bvsdiv(ctx, a, b);
                e        = Z3_mk_extract(ctx, high, low, e);
                return optimize_z3_query(e);
            } else if (n_zero == n_signed) {
                Z3_ast a = ARG1(ARG1(op1));
                Z3_ast b = ARG2(ARG2(op1));
                e        = Z3_mk_bvsdiv(ctx, a, b);
                e        = Z3_mk_extract(ctx, high, low, e);
                return optimize_z3_query(e);
            } else {
                Z3_ast a =
                    Z3_mk_sign_ext(ctx, n_signed - n_zero, ARG1(ARG1(op1)));
                a = optimize_z3_query(a);
                Z3_ast b = ARG2(ARG2(op1));
                e        = Z3_mk_bvsdiv(ctx, a, b);
                e        = Z3_mk_extract(ctx, high, low, e);
                return optimize_z3_query(e);
            }
        }

        // from:
        //   (X op Y)[high:0])
        // where:
        //   - op is in {+, -, *}
        // to:
        //   X[high:0] op Y[high:0]
        if ((OP(op1) == Z3_OP_BADD || OP(op1) == Z3_OP_BSUB ||
             OP(op1) == Z3_OP_BMUL) &&
            low == 0) {

            Z3_ast a =
                optimize_z3_query(Z3_mk_extract(ctx, high, 0, ARG1(op1)));
            Z3_ast b =
                optimize_z3_query(Z3_mk_extract(ctx, high, 0, ARG2(op1)));
            return get_make_op(OP(op1))(ctx, a, b);
        }

        // from:
        //  (X & ffffffffffffff00#64))[7:0]
        // to:
        //  0#8
        if (OP(op1) == Z3_OP_BAND && is_const(ARG2(op1), &value) &&
            value == 0xffffffffffffff00) {

            if (low == 0 && high == 7) {
                return smt_new_const(0, 8);
            }
        }

        // from:
        //  (X & C#N)[high:0]
        // to:
        //  (X[high:0] & C#(high + 1))
        if (OP(op1) == Z3_OP_BAND && is_const(ARG2(op1), &value)) {

            if (low == 0) {
                Z3_ast c = smt_new_const(value, high + 1);
                Z3_ast o = Z3_mk_extract(ctx, high, 0, ARG1(op1));
                o        = optimize_z3_query(o);
                e        = Z3_mk_bvand(ctx, o, c);
                return optimize_z3_query(e);
            }
        }

        // from:
        //  (X ^ C#N)[high:0]
        // to:
        //  (X[high:0] ^ C#(high + 1))
        if (OP(op1) == Z3_OP_BXOR && is_const(ARG2(op1), &value)) {

            if (low == 0) {
                Z3_ast c = smt_new_const(value, high + 1);
                Z3_ast o = Z3_mk_extract(ctx, high, 0, ARG1(op1));
                o        = optimize_z3_query(o);
                e        = Z3_mk_bvxor(ctx, o, c);
                return optimize_z3_query(e);
            }
        }

        // from:
        //  ((0#N .. X) << C#M)[high:0]
        // to:
        //  (X << C#M) iff size(X) == high + 1
        //  ((0#M .. X) << C#M) iff size(X) + M == high + 1
        if (OP(op1) == Z3_OP_BSHL && OP(ARG1(op1)) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG1(op1))) && is_const(ARG2(op1), &value)) {

            if (low == 0 && high + 1 == SIZE(ARG2(ARG1(op1)))) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvshl(ctx, ARG2(ARG1(op1)), c);
                return optimize_z3_query(e);
            }

            if (low == 0 && high + 1 > SIZE(ARG2(ARG1(op1)))) {
                Z3_ast c = smt_new_const(value, high + 1);
                Z3_ast z = smt_new_const(0, (high + 1) - SIZE(ARG2(ARG1(op1))));
                Z3_ast t = Z3_mk_concat(ctx, z, ARG2(ARG1(op1)));
                e        = Z3_mk_bvshl(ctx, t, c);
                return optimize_z3_query(e);
            }
        }

        // from:
        //  ((0#M .. X) >>l C)[high:0]
        // where:
        //  - high + 1 <= size(X)
        //  - high > 7
        // to:
        //  X >>l Y
        if (OP(op1) == Z3_OP_BLSHR && OP(ARG1(op1)) == Z3_OP_CONCAT &&
            is_const(ARG2(op1), &value) && is_zero_const(ARG1(ARG1(op1)))) {

            if (low == 0 && high > 7 && SIZE(ARG2(ARG1(op1))) >= high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvlshr(ctx, ARG2(ARG1(op1)), c);
                return e;
            }
        }

        if (low == 0 && high == 7 && OP(op1) == Z3_OP_BOR && N_ARGS(op1) == 2 &&
            OP(ARG1(op1)) == Z3_OP_BAND && is_const(ARG2(ARG1(op1)), &value) &&
            value == 0xffffffffffffff00) {

            e = Z3_mk_extract(ctx, 7, 0, ARG2(op1));
            return optimize_z3_query(e);
        }

        if (OP(op1) == Z3_OP_ITE) {

            Z3_ast a = Z3_mk_extract(ctx, high, low, ARG2(op1));
            a        = optimize_z3_query(a);
            Z3_ast b = Z3_mk_extract(ctx, high, low, ARG3(op1));
            b        = optimize_z3_query(b);

            if (is_const(a, &value) && is_const(b, &value2) &&
                value == value2) {

                return smt_new_const(value, SIZE(e));
            }
        }

        // from:
        //  ITE(X){ C1 } { C2 }[bit:bit]
        // to:
        //  ITE(X){ C1[bit:bit] }{ C2[bit:bit] }
        if (OP(op1) == Z3_OP_ITE && high == low &&
            is_const(ARG2(op1), &value) && is_const(ARG3(op1), &value2)) {

            Z3_ast c1 = smt_new_const(value >> low, 1);
            Z3_ast c2 = smt_new_const(value2 >> low, 1);
            e         = Z3_mk_ite(ctx, ARG1(op1), c1, c2);
            return optimize_z3_query(e);
        }

        if (low == 0 && OP(op1) == Z3_OP_SIGN_EXT && PARAM1(op1) == high + 1) {

            return ARG1(op1);
        }

        // printf("EXTRACT OPT END\n");

    } else if (decl_kind == Z3_OP_BOR) {
        assert(num_operands == 2);

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        uint64_t value;
        if (is_zero_const(op1)) {
            return op2;
        }
        if (is_const(op1, &value) && value == FF_MASK(SIZE(e))) {
            return op1;
        }
        if (OP(op1) == Z3_OP_EXTRACT && is_zero_const(ARG1(op1))) {
            return op2;
        }
        //
        if (is_zero_const(op2)) {
            return op1;
        }
        if (is_const(op2, &value) && value == FF_MASK(SIZE(e))) {
            return op2;
        }
        if (OP(op2) == Z3_OP_EXTRACT && is_zero_const(ARG1(op2))) {
            return op1;
        }

        Z3_ast  bytes[SHIFT_OPT_MAX_BYTES] = {0};
        uint8_t r = get_shifted_bytes(e, bytes, SHIFT_OPT_MAX_BYTES);
        if (r) {
            int orig_size = SIZE(e);
            int zero_size = 0;
            e             = NULL;
            Z3_ast z;
            for (ssize_t i = (orig_size / 8) - 1; i >= 0; i--) {
                // printf("Index #%lu\n", i);
                if (bytes[i]) {
                    if (zero_size > 0) {
                        z = smt_new_const(0, zero_size);
                        if (e) {
                            e = Z3_mk_concat(ctx, z, e);
                        } else {
                            e = z;
                        }
                        zero_size = 0;
                    }
                    if (e) {
                        e = Z3_mk_concat(ctx, bytes[i], e);
                    } else {
                        e = bytes[i];
                    }
                } else {
                    zero_size += 8;
                }
            }
            if (zero_size > 0) {
                z = smt_new_const(0, zero_size);
                if (e) {
                    e = Z3_mk_concat(ctx, z, e);
                } else {
                    ABORT();
                }
            }
            // print_z3_ast_internal(e, 0);
            // printf("\n");
            assert(SIZE(e) == orig_size);
            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_CONCAT) {

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_const(op1, &value) && num_operands == 2 &&
            OP(op2) == Z3_OP_CONCAT && N_ARGS(op2) == 2 &&
            is_const(ARG1(op2), &value2)) {

            // printf("OPT CONCAT A\n");

            Z3_ast c = NULL;
            if (SIZE(op1) + SIZE(ARG1(op2)) <= 64) {
                value = value << SIZE(ARG1(op2));
                value = value | value2;
                c     = smt_new_const(value, SIZE(op1) + SIZE(ARG1(op2)));
            } else {
                c = Z3_simplify(ctx, Z3_mk_concat(ctx, op1, ARG1(op2)));
            }
            e = Z3_mk_concat(ctx, c, ARG2(op2));
            return optimize_z3_query(e);
        }

        // from:
        //   (Y .. ((0#M .. X)[high:0]))
        // where:
        //   - size(X) == high + 1
        // to:
        //   Y .. X
        if (OP(op2) == Z3_OP_EXTRACT && OP(ARG1(op2)) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG1(op2))) && N_ARGS(e) == 2) {

            // printf("OPT CONCAT B\n");

            int high = PARAM1(op2);
            int low  = PARAM2(op2);
            assert(low >= 0 && high >= low);

            if (low == 0 && SIZE(ARG2(ARG1(op2))) == high + 1) {
                op2 = ARG2(ARG1(op2));
                e   = Z3_mk_concat(ctx, op1, op2);
                return optimize_z3_query(e);
            }

            if (low == 0 && SIZE(ARG2(ARG1(op2))) < high + 1) {
                Z3_ast z = smt_new_const(0, (high + 1) - SIZE(ARG2(ARG1(op2))));
                op2      = Z3_mk_concat(ctx, z, ARG2(ARG1(op2)));
                e        = Z3_mk_concat(ctx, op1, op2);
                return optimize_z3_query(e);
            }
        }

        if (OP(op2) == Z3_OP_CONCAT && is_zero_const(op1) &&
            is_zero_const(ARG1(op2)) && N_ARGS(e) == 2) {

            // printf("OPT CONCAT C\n");

            op1 = smt_new_const(0, SIZE(op1) + SIZE(ARG1(op2)));
            e   = Z3_mk_concat(ctx, op1, ARG2(op2));
            return optimize_z3_query(e);
        }

        if (N_ARGS(e) == 2 && OP(op1) == Z3_OP_BASHR &&
            is_const(ARG2(op1), &value) && value == (SIZE(op2) - 1) &&
            ARG1(op1) == op2) {

            // printf("OPT CONCAT D\n");

            e = Z3_mk_sign_ext(ctx, SIZE(op1), op2);
            return optimize_z3_query(e);
        }

        if (N_ARGS(e) == 2 && OP(op1) == Z3_OP_CONCAT &&
            OP(op2) != Z3_OP_CONCAT) {

            // printf("OPT CONCAT E\n");

            Z3_ast a = ARG1(op1);
            Z3_ast b = Z3_mk_concat(ctx, ARG2(op1), op2);
            b        = optimize_z3_query(b);
            e        = Z3_mk_concat(ctx, a, b);
            return optimize_z3_query(e);
        }

        if (N_ARGS(e) == 2 && OP(op1) == Z3_OP_EXTRACT &&
            OP(op2) == Z3_OP_EXTRACT && ARG1(op1) == ARG1(op2) &&
            PARAM2(op1) == PARAM1(op2) + 1) {

            // printf("OPT CONCAT G\n");

            e = Z3_mk_extract(ctx, PARAM1(op1), PARAM2(op2), ARG1(op1));
            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_BAND) {

        if (N_ARGS(e) != 2) {
            return e;
        }

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        uint64_t value, value2;
        if (is_const(op1, &value) && is_const(op2, &value2)) {
            return smt_new_const(value & value2, SIZE(e));
        }

        if (is_zero_const(op1)) {
            return op1;
        }

        if (is_zero_const(op2)) {
            return op2;
        }

        if (is_const(op1, &value)) {
            if (value == FF_MASK(SIZE(op1))) {
                return op2;
            } else if (value == 0x1) {
                e           = Z3_mk_extract(ctx, 0, 0, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op1) - 1);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0x7) {
                e           = Z3_mk_extract(ctx, 2, 0, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op1) - 3);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0xF) {
                e           = Z3_mk_extract(ctx, 3, 0, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op1) - 4);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0x3F) {
                e           = Z3_mk_extract(ctx, 5, 0, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op1) - 6);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0xFF) {
                e           = Z3_mk_extract(ctx, 7, 0, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op1) - 8);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0xfffffffffffffff8) {
                e           = Z3_mk_extract(ctx, 63, 3, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, 3);
                e           = Z3_mk_concat(ctx, e, zero);
                return optimize_z3_query(e);
            } else if (value == 0xfffffffffffffff0) {
                e           = Z3_mk_extract(ctx, 63, 4, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, 4);
                e           = Z3_mk_concat(ctx, e, zero);
                return optimize_z3_query(e);
            } else if (value == 0xffffffffffffff00) {
                e           = Z3_mk_extract(ctx, 63, 8, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, 8);
                e           = Z3_mk_concat(ctx, e, zero);
                return optimize_z3_query(e);
            } else if (value == 0xffffffffffffffc0) {
                e           = Z3_mk_extract(ctx, 63, 6, op2);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, 6);
                e           = Z3_mk_concat(ctx, e, zero);
                return optimize_z3_query(e);
            }
        }

        if (is_const(op2, &value)) {
            if (value == FF_MASK(SIZE(op2))) {
                return op1;
            } else if (value == 0x1) {
                e           = Z3_mk_extract(ctx, 0, 0, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op2) - 1);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0x7) {
                e           = Z3_mk_extract(ctx, 2, 0, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op2) - 3);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0xF) {
                e           = Z3_mk_extract(ctx, 3, 0, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op2) - 4);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0x3F) {
                e           = Z3_mk_extract(ctx, 5, 0, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op2) - 6);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0xFF) {
                e           = Z3_mk_extract(ctx, 7, 0, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, SIZE(op2) - 8);
                e           = Z3_mk_concat(ctx, zero, e);
                return optimize_z3_query(e);
            } else if (value == 0xfffffffffffffff8) {
                e           = Z3_mk_extract(ctx, 63, 3, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, 3);
                e           = Z3_mk_concat(ctx, e, zero);
                return optimize_z3_query(e);
            } else if (value == 0xfffffffffffffff0) {
                e           = Z3_mk_extract(ctx, 63, 4, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, 4);
                e           = Z3_mk_concat(ctx, e, zero);
                return optimize_z3_query(e);
            } else if (value == 0xffffffffffffff00) {
                e           = Z3_mk_extract(ctx, 63, 8, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, 8);
                e           = Z3_mk_concat(ctx, e, zero);
                return optimize_z3_query(e);
            } else if (value == 0xffffffffffffffc0) {
                e           = Z3_mk_extract(ctx, 63, 6, op1);
                e           = optimize_z3_query(e);
                Z3_ast zero = smt_new_const(0, 6);
                e           = Z3_mk_concat(ctx, e, zero);
                return optimize_z3_query(e);
            }
        }

        // from:
        //   (if (X) { C1#N } else { C2#N }) & 0xff#N
        // where:
        //   C1 < 0xff && C2 < 0xff
        // to:
        //  if (X) { C1#N } else { C2#N }
        if (OP(op1) == Z3_OP_ITE && is_const(op2, &value) && value == 0xFF &&
            is_const(ARG2(op1), &value) && value <= 0xFF &&
            is_const(ARG3(op1), &value2) && value2 <= 0xFF) {

            Z3_ast c1 = smt_new_const(value, SIZE(e));
            Z3_ast c2 = smt_new_const(value2, SIZE(e));
            e         = Z3_mk_ite(ctx, ARG1(op1), c1, c2);
            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_ITE) {

        if (is_const(ARG1(e), &value)) {
            if (value) {
                return ARG2(e);
            } else {
                return ARG3(e);
            }
        }

        if (OP(ARG1(e)) == Z3_OP_TRUE) {
            return ARG2(e);
        }

        if (OP(ARG1(e)) == Z3_OP_FALSE) {
            return ARG3(e);
        }

    } else if (decl_kind == Z3_OP_SIGN_EXT) {

        Z3_ast   op1 = ARG1(e);
        unsigned n   = PARAM1(e);

        if (OP(op1) == Z3_OP_CONCAT && is_zero_const(ARG1(op1))) {

            Z3_ast zero = smt_new_const(0, n);
            e           = Z3_mk_concat(ctx, zero, op1);
            return optimize_z3_query(e);
        }

        Z3_ast msb = Z3_mk_extract(ctx, SIZE(op1) - 1, SIZE(op1) - 1, op1);
        msb        = optimize_z3_query(msb);

        if (is_const(msb, &value)) {
            if (value == 0) {
                Z3_ast c = smt_new_const(0, n);
                return Z3_mk_concat(ctx, c, op1);
            } else if (SIZE(e) <= 64) {
                Z3_ast c = smt_new_const(FF_MASK(n), n);
                return Z3_mk_concat(ctx, c, op1);
            }
        }

    } else if (decl_kind == Z3_OP_BADD) {

        Z3_ast  bytes[SHIFT_OPT_MAX_BYTES] = {0};
        uint8_t r = get_shifted_bytes(e, bytes, SHIFT_OPT_MAX_BYTES);
        if (r) {
            int orig_size = SIZE(e);
            int zero_size = 0;
            e             = NULL;
            Z3_ast z;
            for (ssize_t i = (orig_size / 8) - 1; i >= 0; i--) {
                // printf("Index #%lu\n", i);
                if (bytes[i]) {
                    if (zero_size > 0) {
                        // printf("A zero_size=%u\n", zero_size);
                        z = smt_new_const(0, zero_size);
                        if (e) {
                            e = Z3_mk_concat(ctx, z, e);
                        } else {
                            e = z;
                        }
                        zero_size = 0;
                    }
                    if (e) {
                        e = Z3_mk_concat(ctx, bytes[i], e);
                    } else {
                        e = bytes[i];
                    }
                } else {
                    zero_size += 8;
                }
            }
            if (zero_size > 0) {
                z = smt_new_const(0, zero_size);
                if (e) {
                    e = Z3_mk_concat(ctx, z, e);
                } else {
                    ABORT();
                }
            }
            assert(SIZE(e) == orig_size);
            return optimize_z3_query(e);
        }

        assert(N_ARGS(e) == 2);
        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_const(ARG2(e), &value) && OP(ARG1(e)) == Z3_OP_BADD &&
            N_ARGS(ARG1(e)) == 2 && is_const(ARG2(ARG1(e)), &value2)) {

            e = Z3_mk_bvadd(ctx, ARG1(ARG1(e)),
                            smt_new_const(value + value2, SIZE(e)));
            return optimize_z3_query(e);
        }

        if (is_const(ARG2(e), &value) && OP(ARG1(e)) == Z3_OP_BSUB &&
            N_ARGS(ARG1(e)) == 2 && is_const(ARG2(ARG1(e)), &value2)) {

            e = Z3_mk_bvsub(ctx, ARG1(ARG1(e)),
                            smt_new_const(value2 - value, SIZE(e)));
            return optimize_z3_query(e);
        }

        if (OP(op1) == Z3_OP_CONCAT && N_ARGS(op1) == 2 &&
            is_zero_const(ARG2(op1)) && is_const(op2, &value) &&
            value <= FF_MASK(SIZE(ARG2(op1)))) {

            Z3_ast a = ARG1(op1);
            Z3_ast b = smt_new_const(value, SIZE(ARG2(op1)));
            e        = Z3_mk_concat(ctx, a, b);
            return optimize_z3_query(e);
        }

        if (is_const(op2, &value) && value < 8) {

            Z3_ast a = Z3_mk_extract(ctx, 2, 0, op1);
            a        = optimize_z3_query(a);
            if (is_zero_const(a)) {
                e = Z3_mk_extract(ctx, SIZE(op1) - 1, 3, op1);
                e = optimize_z3_query(e);
                e = Z3_mk_concat(ctx, e, smt_new_const(value, 3));
                e = optimize_z3_query(e);
                return e;
            }
        }

        if (op1 == op2) {
            e = Z3_mk_bvshl(ctx, op1, smt_new_const(1, SIZE(op1)));
            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_BSUB) {

        assert(N_ARGS(e) == 2);
        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_const(ARG2(e), &value) && OP(ARG1(e)) == Z3_OP_BADD &&
            N_ARGS(ARG1(e)) == 2 && is_const(ARG2(ARG1(e)), &value2)) {

            e = Z3_mk_bvadd(ctx, ARG1(ARG1(e)),
                            smt_new_const(value2 - value, SIZE(e)));
            return optimize_z3_query(e);
        }

        if (is_const(ARG2(e), &value) && OP(ARG1(e)) == Z3_OP_BSUB &&
            N_ARGS(ARG1(e)) == 2 && is_const(ARG2(ARG1(e)), &value2)) {

            e = Z3_mk_bvsub(ctx, ARG1(ARG1(e)),
                            smt_new_const(value2 + value, SIZE(e)));
            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_BASHR) {

        assert(N_ARGS(e) == 2);
        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_const(op2, &value)) {

            if (value == 0) {
                return op1;
            }

            Z3_ast msb = Z3_mk_extract(ctx, SIZE(op1) - 1, SIZE(op1) - 1, op1);
            msb        = optimize_z3_query(msb);

            if (is_const(msb, &value2)) {
                if (value == SIZE(e) - 1) {
                    if (value2 == 0) {
                        return smt_new_const(0, SIZE(e));
                    } else if (SIZE(e) <= 64) {
                        return smt_new_const(FF_MASK(SIZE(e)), SIZE(e));
                    }
                } else {
                    if (value2 == 0) {
                        Z3_ast a = smt_new_const(0, value);
                        Z3_ast b =
                            Z3_mk_extract(ctx, SIZE(op1) - 1, value, op1);
                        b = optimize_z3_query(b);
                        e = Z3_mk_concat(ctx, a, b);
                        return e;
                    } else if (SIZE(e) <= 64) {
                        Z3_ast a = smt_new_const(FF_MASK(value), value);
                        Z3_ast b =
                            Z3_mk_extract(ctx, SIZE(op1) - 1, value, op1);
                        b = optimize_z3_query(b);
                        e = Z3_mk_concat(ctx, a, b);
                        return e;
                    }
                }
            }
        }

    } else if (decl_kind == Z3_OP_BSHL) {

        assert(N_ARGS(e) == 2);
        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_const(op2, &value)) {

            if (value == 0) {
                return op1;
            }

            Z3_ast a = Z3_mk_extract(ctx, SIZE(op1) - value - 1, 0, op1);
            a        = optimize_z3_query(a);
            Z3_ast b = smt_new_const(0, value);

            e = Z3_mk_concat(ctx, a, b);

            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_BMUL) {

        assert(N_ARGS(e) == 2);
        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_zero_const(op1)) {
            return op1;
        }

        if (is_zero_const(op2)) {
            return op2;
        }

        if (is_const(op1, &value) && value == 1) {
            return op2;
        }

        if (is_const(op2, &value) && value == 1) {
            return op1;
        }

#define IS_POWER_OF_TWO(x) ((((uint64_t)x) & (((uint64_t)x) - 1)) == 0)
#define LOG2(X)            ((unsigned)(8 * sizeof(uint64_t) - __builtin_clzll((X)) - 1))

        if (is_const(op1, &value) && IS_POWER_OF_TWO(value) &&
            value <= FF_MASK(64)) {
            Z3_ast a = Z3_mk_extract(ctx, SIZE(op2) - 1 - LOG2(value), 0, op2);
            a        = optimize_z3_query(a);
            Z3_ast b = smt_new_const(0, SIZE(e) - SIZE(a));
            e        = Z3_mk_concat(ctx, a, b);
            return optimize_z3_query(e);
        }

        if (is_const(op2, &value) && IS_POWER_OF_TWO(value) &&
            value <= FF_MASK(63)) {
            Z3_ast a = Z3_mk_extract(ctx, SIZE(op1) - 1 - LOG2(value), 0, op1);
            a        = optimize_z3_query(a);
            Z3_ast b = smt_new_const(0, SIZE(e) - SIZE(a));
            e        = Z3_mk_concat(ctx, a, b);
            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_BUDIV || decl_kind == Z3_OP_BSDIV) {

        assert(N_ARGS(e) == 2);
        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_zero_const(op1)) {
            return op1;
        }

        if (is_const(op2, &value) && IS_POWER_OF_TWO(value)) {

            if (value == 1) {
                return op1;
            }

            if (decl_kind == Z3_OP_BUDIV) {
                unsigned n = LOG2(value);
                Z3_ast   a = smt_new_const(0, n);
                Z3_ast   b = Z3_mk_extract(ctx, SIZE(op1) - 1, n, op1);
                b          = optimize_z3_query(b);
                e          = Z3_mk_concat(ctx, a, b);
                return optimize_z3_query(e);
            } else {
                Z3_ast msb =
                    Z3_mk_extract(ctx, SIZE(op1) - 1, SIZE(op1) - 1, op1);
                msb = optimize_z3_query(msb);
                if (is_const(msb, &value2)) {
                    unsigned n = LOG2(value);
                    Z3_ast   a = NULL;
                    if (value2 == 0) {
                        a = smt_new_const(0, n);
                    } else if (value <= FF_MASK(63)) {
                        a = smt_new_const(FF_MASK(n), n);
                    }
                    if (a) {
                        Z3_ast b = Z3_mk_extract(ctx, SIZE(op1) - 1, n, op1);
                        b        = optimize_z3_query(b);
                        e        = Z3_mk_concat(ctx, a, b);
                        return optimize_z3_query(e);
                    }
                }
            }
        }

    } else if (decl_kind == Z3_OP_BUREM || decl_kind == Z3_OP_BSREM) {

        assert(N_ARGS(e) == 2);
        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_zero_const(op1)) {
            return op1;
        }

        if (is_const(op2, &value) && value < FF_MASK(SIZE(e)) &&
            IS_POWER_OF_TWO(value)) {

            if (value == 1) {
                return smt_new_const(0, SIZE(e));
            }

            if (decl_kind == Z3_OP_BUREM) {
                unsigned n = LOG2(value);
                Z3_ast   b = Z3_mk_extract(ctx, n - 1, 0, op1);
                b          = optimize_z3_query(b);
                Z3_ast a   = smt_new_const(0, SIZE(e) - SIZE(b));
                e          = Z3_mk_concat(ctx, a, b);
                return optimize_z3_query(e);
            }
        }

    } else if (decl_kind == Z3_OP_BLSHR) {

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_const(op2, &value)) {

            if (value == 0) {
                return op1;
            }

            Z3_ast a = smt_new_const(0, value);
            Z3_ast b = Z3_mk_extract(ctx, SIZE(op1) - 1, value, op1);
            b        = optimize_z3_query(b);
            e        = Z3_mk_concat(ctx, a, b);
            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_BXOR) {

        assert(N_ARGS(e) == 2);
        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        if (is_zero_const(op1)) {
            return op2;
        }

        if (is_zero_const(op2)) {
            return op1;
        }
    }

    return e;
}

static inline size_t scale_sload_index(size_t index)
{
    index = index - MAX_INPUT_SIZE;
    assert(index < MAX_INPUTS_EXPRS);
    index = testcase.size + (index * 2);
    return index;
}

static inline size_t reverse_scale_sload_index(size_t index)
{
    index = index - testcase.size;
    index = index >> 1;
    index = index + MAX_INPUT_SIZE;
    return index;
}

Z3_ast smt_query_to_z3_wrapper(Expr* query, uintptr_t is_const_value,
                               size_t width, GHashTable** inputs)
{
    if (debug_translation) {
        print_expr(query);
    }

    GHashTable* ptr = NULL;
    if (!inputs) {
        inputs = &ptr;
    }

    // printf("Translating...\n");
    struct timespec start, end;
    get_time(&start);
    Z3_ast r = smt_query_to_z3(query, is_const_value, width, inputs);
    get_time(&end);
    uint64_t elapsed = get_diff_time_microsec(&start, &end);
    smt_solver.translation_time += elapsed;
    // printf("Translation time: %lu us (cumulative: %lu us)\n", elapsed,
    //       smt_solver.translation_time);
    return r;
}

void get_inputs_from_expr(Z3_ast e, GHashTable* inputs)
{
    if (!inputs) {
        return;
    }

    Z3_context  ctx  = smt_solver.ctx;
    Z3_ast_kind kind = Z3_get_ast_kind(ctx, e);

    if (kind != Z3_APP_AST) {
        return;
    }

    // print_z3_ast(e);

    Z3_decl_kind decl_kind = OP(e);
    switch (decl_kind) {
        case Z3_OP_UNINTERPRETED: {
            Z3_func_decl decl   = Z3_get_app_decl(ctx, APP(e));
            Z3_symbol    symbol = Z3_get_decl_name(ctx, decl);
            uint64_t     k      = Z3_get_symbol_int(ctx, symbol);
            g_hash_table_add(inputs, (gpointer)k);
            break;
        }
        default: {
            unsigned num_operands = N_ARGS(e);
            for (size_t i = 0; i < num_operands; i++) {
                Z3_ast child = Z3_get_app_arg(ctx, APP(e), i);
                get_inputs_from_expr(child, inputs);
            }
        }
    }
}

GHashTable* merge_inputs(GHashTable* a, GHashTable* b)
{
    if (a == NULL)
        return b;
    if (b == NULL)
        return a;
    GHashTable* merged = g_hash_table_new(NULL, NULL);

    GHashTableIter iter;
    gpointer       key, value;

    if (g_hash_table_size(a) == g_hash_table_size(b)) {
        int different = 0;
        g_hash_table_iter_init(&iter, b);
        while (g_hash_table_iter_next(&iter, &key, &value)) {
            if (g_hash_table_contains(a, key) == FALSE) {
                different = 1;
                break;
            }
        }
        if (!different) {
            return a;
        }
    }

    g_hash_table_iter_init(&iter, a);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        g_hash_table_add(merged, (gpointer)key);
    }
    g_hash_table_iter_init(&iter, b);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        g_hash_table_add(merged, (gpointer)key);
    }
    return merged;
}

#define VERBOSE 0
Z3_ast smt_query_to_z3(Expr* query, uintptr_t is_const_value, size_t width,
                       GHashTable** inputs)
{
    assert(inputs && *inputs == NULL);
    CachedExpr* ce = g_hash_table_lookup(z3_expr_cache, (gpointer)query);
    if (ce) {
        *inputs = ce->inputs;
        return ce->expr;
    }

    if (width <= 0)
        width = sizeof(void*);

    if (is_const_value) {
        // printf("IS_CONST: %lx\n", (uintptr_t)query);
        return smt_new_const((uintptr_t)query, 8 * width);
    }

    if (query == NULL)
        return Z3_mk_true(smt_solver.ctx);

    if (debug_translation) {
        print_expr(query);
    }

    // printf("START opkind: %s\n", opkind_to_str(query->opkind));

    Z3_ast      r          = NULL;
    Z3_ast      op1        = NULL;
    Z3_ast      op2        = NULL;
    GHashTable* op1_inputs = NULL;
    GHashTable* op2_inputs = NULL;
    unsigned    n          = 0;
    switch (query->opkind) {
        case RESERVED:
            ABORT("Invalid opkind (RESERVER). There is a bug somewhere :(");
        case IS_SYMBOLIC:;
            uintptr_t id = CONST(query->op1);
            if (id >= testcase.size) {
                id = scale_sload_index(id);
            }
            uintptr_t n_bytes = CONST(query->op2);
            if (concretized_sloads[id]) {
                r = smt_new_const(CONST(query->op3), 8 * n_bytes);
            } else if (concretized_iloads[id]) {
                // should be in the cache!
                printf("Expr ID: %lu\n", GET_EXPR_IDX(query));
                ABORT();
            } else {
                r          = smt_new_symbol_int(id, 8 * n_bytes, query);
                op1_inputs = g_hash_table_new(NULL, NULL);
                g_hash_table_add(op1_inputs, (gpointer)id);
            }
            break;
        case IS_CONST:
            r = smt_new_const(CONST(query->op1), 8);
            break;
        //
        case NOT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            assert(query->op2 == 0);
#if VERBOSE
            printf("NOT\n");
            smt_print_ast_sort(op1);
#endif
            r = Z3_mk_bvnot(smt_solver.ctx, op1);
            break;
        //
        case NEG:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            assert(query->op2 == 0);
            op1 = smt_to_bv_n(op1, 8);
#if VERBOSE
            printf("NEG\n");
            smt_print_ast_sort(op1);
#endif
            r = Z3_mk_bvneg(smt_solver.ctx, op1);
            break;
        //
        case ADD:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, (ssize_t)query->op3);
#if VERBOSE
            printf("ADD\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = NULL;
            uint64_t value, value2;
            if (is_const(op1, &value)) {
                if (value == 0) {
                    r = op2;
                } else if (OP(op2) == Z3_OP_BADD) {
                    if (is_const(ARG1(op2), &value2)) {
                        Z3_ast c = smt_new_const(value + value2, SIZE(op1));
                        r        = Z3_mk_bvadd(smt_solver.ctx, c, ARG2(op2));
                    } else if (is_const(ARG2(op2), &value2)) {
                        Z3_ast c = smt_new_const(value + value2, SIZE(op1));
                        r        = Z3_mk_bvadd(smt_solver.ctx, ARG1(op2), c);
                    }
                }
            } else if (is_const(op2, &value)) {
                if (value == 0) {
                    r = op1;
                } else if (OP(op1) == Z3_OP_BADD) {
                    if (is_const(ARG1(op1), &value2)) {
                        Z3_ast c = smt_new_const(value + value2, SIZE(op1));
                        r        = Z3_mk_bvadd(smt_solver.ctx, c, ARG2(op1));
                    } else if (is_const(ARG2(op1), &value2)) {
                        Z3_ast c = smt_new_const(value + value2, SIZE(op1));
                        r        = Z3_mk_bvadd(smt_solver.ctx, ARG1(op1), c);
                    }
                }
            }
            if (!r) {
                r = Z3_mk_bvadd(smt_solver.ctx, op1, op2);
            }
            break;
        case SUB:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, (ssize_t)query->op3);
#if VERBOSE
            printf("SUB\n");
            printf("size=%ld\n", (ssize_t)query->op3);
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvsub(smt_solver.ctx, op1, op2);
            break;
        case MUL:
        case MULU:
            op1       = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2       = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            ssize_t s = (ssize_t)query->op3;
            assert(s >= 0);
            smt_bv_resize(&op1, &op2, (ssize_t)query->op3);
#if VERBOSE
            printf("MUL\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvmul(smt_solver.ctx, op1, op2);
            break;
        case DIVU: // 8
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("DIVU\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvudiv(smt_solver.ctx, op1, op2);
            break;
        case DIV:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("\nDIV\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
            print_z3_ast(op1);
            print_z3_ast(op2);
            printf("DIV DONE\n\n");
#endif
            r = Z3_mk_bvsdiv(smt_solver.ctx, op1, op2);
            break;
        case REMU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("REMU\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvurem(smt_solver.ctx, op1, op2);
            break;
        case REM:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("\nREM\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
            print_z3_ast(op1);
            print_z3_ast(op2);
            printf("REM DONE\n\n");
#endif
            r = Z3_mk_bvsrem(smt_solver.ctx, op1, op2);
            break;
        case AND:;
            ExprAnnotation* ea = NULL;
            if (query->op2_is_const) {
                // optimization for eflags extraction
                ea        = calloc(sizeof(ExprAnnotation), 1);
                ea->type  = COSTANT_AND;
                ea->value = (uintptr_t)query->op2;
                add_expr_annotation(query->op1, ea);
            }

            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);

            if (ea && ea->result) {
                assert(Z3_get_sort_kind(smt_solver.ctx,
                                        Z3_get_sort(smt_solver.ctx, op1)) !=
                       Z3_BOOL_SORT);
                // printf("EFLAGS: optimized flag extraction\n");
                r = ea->result;
            } else {
                op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                      &op2_inputs);
                smt_bv_resize(&op1, &op2, CONST(query->op3));
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
                } else {
                    smt_bv_resize(&op1, &op2, 0);
                    r = Z3_mk_bvand(smt_solver.ctx, op1, op2);
                }
            }

            if (ea) {
                add_expr_annotation(query->op1, NULL);
                free(ea);
            }

            break;
        case OR: // 12
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(((ssize_t)query->op3) >= 0);
            smt_bv_resize(&op1, &op2, (ssize_t)query->op3);
#if VERBOSE
            printf("OR\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvor(smt_solver.ctx, op1, op2);
            break;
        case XOR: // 13
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("XOR\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvxor(smt_solver.ctx, op1, op2);
            break;
        case SHL: // 14
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, (ssize_t)query->op3);
#if VERBOSE
            printf("SHL\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvshl(smt_solver.ctx, op1, op2);
            break;
        case SHR: // 15
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, (ssize_t)query->op3);
#if VERBOSE
            printf("SHR\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvlshr(smt_solver.ctx, op1, op2);
            break;
        case SAR:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, (ssize_t)query->op3);
#if VERBOSE
            printf("SAR\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvashr(smt_solver.ctx, op1, op2);
            break;
        case ROTL: // 17
            assert(query->op2_is_const && "Second arg of ROL must be concrete");
            op2     = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            int pos = (int)(long long)query->op2;
            r       = Z3_mk_rotate_left(smt_solver.ctx, pos, op2);
            break;
        //
        case EQ:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, CONST(query->op3));
#if VERBOSE
            printf("EQ\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_eq(smt_solver.ctx, smt_to_bv(op1), smt_to_bv(op2));
            break;
        case NE:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, CONST(query->op3));
#if VERBOSE
            printf("NE\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_not(
                smt_solver.ctx,
                Z3_mk_eq(smt_solver.ctx, smt_to_bv(op1), smt_to_bv(op2)));
            break;
        //
        case LT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("LT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvslt(smt_solver.ctx, op1, op2);
            break;
        //
        case LE:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("LE\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvsle(smt_solver.ctx, op1, op2);
            break;
        case GE:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("LT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvsge(smt_solver.ctx, smt_to_bv(op1), smt_to_bv(op2));
            break;
        case GT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("GT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvsgt(smt_solver.ctx, smt_to_bv(op1), smt_to_bv(op2));
            break;
        //
        case LTU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("LTU\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvult(smt_solver.ctx, op1, op2);
            break;
        case LEU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("LEU\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvule(smt_solver.ctx, op1, op2);
            break;
        case GEU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("GEU\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvuge(smt_solver.ctx, op1, op2);
            break;
        case GTU:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("GTU\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvugt(smt_solver.ctx, op1, op2);
            break;
        //
        case ZEXT:
            if (query->op1->opkind == ZEXT &&
                (uintptr_t)query->op2 == (uintptr_t)query->op1->op2) {
                op1 = smt_query_to_z3(query->op1->op1, query->op1->op1_is_const,
                                      0, &op1_inputs);
            } else {
                op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                      &op1_inputs);
            }
            unsigned n = (uintptr_t)query->op2;
#if VERBOSE
            printf("EXTRACT + ZEXT\n");
            smt_print_ast_sort(op1);
#endif
            size_t size;
            if (IS_BOOL(op1)) {
                op1  = smt_to_bv(op1);
                size = 8;
            } else {
                Z3_sort sort = Z3_get_sort(smt_solver.ctx, op1);
                size         = Z3_get_bv_sort_size(smt_solver.ctx, sort);
            }
            if (size >= n) {
                if (size > n) {
                    op1 = Z3_mk_extract(smt_solver.ctx, n - 1, 0, op1);
                    op1 = optimize_z3_query(op1);
                }
                op2 = smt_new_const(0, 64 - n);
                r   = Z3_mk_concat(smt_solver.ctx, op2, op1);
            } else if (size < n) {
                op2 = smt_new_const(0, 64 - size);
                r   = Z3_mk_concat(smt_solver.ctx, op2, op1);
            }
            break;
        case SEXT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            n   = (uintptr_t)query->op2;
            op1 = Z3_mk_extract(smt_solver.ctx, n - 1, 0, op1);
            op1 = optimize_z3_query(op1);
#if VERBOSE
            printf("EXTRACT + SEXT\n");
            smt_print_ast_sort(op1);
#endif
            r = Z3_mk_sign_ext(smt_solver.ctx, 64 - n, op1);
            break;
        case CONCAT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            op1 = smt_to_bv(op1);
            op2 = smt_to_bv(op2);
#if VERBOSE
            printf("CONCAT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_concat(smt_solver.ctx, op1, op2);
            break;
        case CONCAT8R:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 1,
                                  &op2_inputs);
#if VERBOSE
            printf("CONCAT8R\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_concat(smt_solver.ctx, op1, op2);
            break;
        case CONCAT8L:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 1,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
#if VERBOSE
            printf("CONCAT8L\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_concat(smt_solver.ctx, op1, op2);
            break;
        case EXTRACT8:
            op1           = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            unsigned high = ((((uintptr_t)query->op2) + 1) * 8) - 1;
            unsigned low  = ((uintptr_t)query->op2) * 8;
#if VERBOSE
            printf("EXTRACT8\n");
            smt_print_ast_sort(op1);
#endif
            r = Z3_mk_extract(smt_solver.ctx, high, low, op1);
            break;
        case EXTRACT:
            op1  = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            high = (uintptr_t)query->op2;
            low  = (uintptr_t)query->op3;
#if VERBOSE
            printf("EXTRACT: high=%u low=%u\n", high, low);
            smt_print_ast_sort(op1);
#endif
            if (low == 0 && SIZE(op1) == high + 1) {
                r = op1;
            } else {
                r = Z3_mk_extract(smt_solver.ctx, high, low, op1);
            }
            break;
        case DEPOSIT:
            // DEPOSIT(arg0, arg1, arg2, pos, len):
            //    arg0 = (arg1 & ~MASK(pos, len)) | ((arg2 << pos) & MASK(pos,
            //    len))
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            op2 = smt_to_bv(op2);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("DEPOSIT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            uintptr_t dpos = UNPACK_0((uint64_t)query->op3);
            uintptr_t dlen = UNPACK_1((uint64_t)query->op3);
            Z3_ast    r0 =
                Z3_mk_bvand(smt_solver.ctx, op1,
                            smt_new_const(~DEPOSIT_MASK(dpos, dlen), 64));
            Z3_ast r1 =
                Z3_mk_bvshl(smt_solver.ctx, op2, smt_new_const(dpos, 64));
            r1 = Z3_mk_bvand(smt_solver.ctx, op2,
                             smt_new_const(DEPOSIT_MASK(dpos, dlen), 64));
            r0 = optimize_z3_query(r0);
            r1 = optimize_z3_query(r1);
            r  = Z3_mk_bvor(smt_solver.ctx, r0, r1);
            break;
        //
        case QZEXTRACT: {
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            if (SIZE(op1) < 64) {
                op1 = Z3_mk_concat(smt_solver.ctx,
                                   smt_new_const(0, 64 - SIZE(op1)), op1);
            }
            size_t pos = CONST(query->op2);
            size_t len = CONST(query->op3);
#if VERBOSE
            printf("QZEXTRACT: pos=%lu len=%lu\n", pos, len);
            smt_print_ast_sort(op1);
#endif
            // (arg1 << (N_BITS-(pos+len))) >> (N_BITS-len)
            r = Z3_mk_bvshl(smt_solver.ctx, op1,
                            smt_new_const(64 - (pos + len), 64));
            r = Z3_mk_bvlshr(smt_solver.ctx, r, smt_new_const(64 - len, 64));
            break;
        }
        //
        case QZEXTRACT2:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, 8);
            dpos = (uintptr_t)query->op3;
#if VERBOSE
            printf("QZEXTRACT2: %lu\n", dpos);
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_concat(smt_solver.ctx, op2, op1);
            r = Z3_mk_extract(smt_solver.ctx, dpos + 64 - 1, dpos, r);
            break;
        //
        case MUL_HIGH:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, 8);
            if (query->op3 != 0 && CONST(query->op3) != 8) {
                ssize_t s = (ssize_t)query->op3;
                if (s < 0)
                    s = -s;
                op1 = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, op1);
                op1 = optimize_z3_query(op1);
                op2 = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, op2);
                op2 = optimize_z3_query(op2);
                op1 = Z3_mk_sign_ext(smt_solver.ctx, 64 - (s * 8), op1);
                op1 = optimize_z3_query(op1);
                op2 = Z3_mk_sign_ext(smt_solver.ctx, 64 - (s * 8), op2);
                op2 = optimize_z3_query(op2);
            } else {
                op1 = Z3_mk_sign_ext(smt_solver.ctx, 64, op1);
                op2 = Z3_mk_sign_ext(smt_solver.ctx, 64, op2);
            }
#if VERBOSE
            printf("MUL_HIGH\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvmul(smt_solver.ctx, op1, op2);
            r = optimize_z3_query(r);
            if (query->op3 != 0 && CONST(query->op3) != 8) {
                ssize_t s = (ssize_t)query->op3;
                if (s > 0) {
                    assert(0);
                    r = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, r);
                } else {
                    s = -s;
                    r = Z3_mk_extract(smt_solver.ctx, 2 * (s * 8) - 1, s * 8,
                                      r);
                }
            } else {
                r = Z3_mk_extract(smt_solver.ctx, 127, 64, r);
            }
#if 0
            if (CONST(query->op3) != 0 && CONST(query->op3) != 8) {
                ssize_t s = (ssize_t)query->op3;
                if (s < 0) s = -s;
                if (SIZE(r) != (8 * s)) {
                    print_z3_ast(r);
                    ABORT();
                }
            }
#endif
            break;
        case MULU_HIGH:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, 8);
            if (query->op3 != 0 && CONST(query->op3) != 8) {
                ssize_t s = (ssize_t)query->op3;
                if (s < 0)
                    s = -s;
                op1 = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, op1);
                op1 = optimize_z3_query(op1);
                op2 = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, op2);
                op2 = optimize_z3_query(op2);
                op1 = Z3_mk_concat(smt_solver.ctx,
                                   smt_new_const(0, 64 - (s * 8)), op1);
                op1 = optimize_z3_query(op1);
                op2 = Z3_mk_concat(smt_solver.ctx,
                                   smt_new_const(0, 64 - (s * 8)), op2);
                op2 = optimize_z3_query(op2);
            } else {
                op1 = Z3_mk_concat(smt_solver.ctx, smt_new_const(0, 64), op1);
                op1 = optimize_z3_query(op1);
                op2 = Z3_mk_concat(smt_solver.ctx, smt_new_const(0, 64), op2);
                op2 = optimize_z3_query(op2);
            }
#if VERBOSE
            printf("MULU_HIGH\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvmul(smt_solver.ctx, op1, op2);
            r = optimize_z3_query(r);
            if (query->op3 != 0 && CONST(query->op3) != 8) {
                ssize_t s = (ssize_t)query->op3;
                if (s > 0) {
                    assert(0);
                    r = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, r);
                } else {
                    s = -s;
                    r = Z3_mk_extract(smt_solver.ctx, 2 * (s * 8) - 1, s * 8,
                                      r);
                }
            } else {
                r = Z3_mk_extract(smt_solver.ctx, 127, 64, r);
            }
            break;
        //
        case CLZ: {
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
#if VERBOSE
            printf("CLZ\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            if (op1 != op2) {
                ABORT("Not yet implemented");
            } else {
                // ToDo
                for (size_t i = 0; i < SIZE(op1); i++) {
                    Z3_ast byte =
                        Z3_mk_extract(smt_solver.ctx, SIZE(op1) - 1 - i,
                                      SIZE(op1) - 1 - i, op1);
                    byte = optimize_z3_query(byte);

                    size_t k = SIZE(op1) - i - 1;
                    if (is_zero_const(byte)) {
                        if (i == 0) {
                            r = smt_new_const(k + 1, SIZE(op1));
                        }
                    } else {
                        byte =
                            Z3_mk_eq(smt_solver.ctx, byte, smt_new_const(0, 1));
                        byte = optimize_z3_query(byte);
                        if (i == 0) {
                            r = Z3_mk_ite(smt_solver.ctx, byte,
                                          smt_new_const(k + 1, SIZE(op1)),
                                          smt_new_const(k, SIZE(op1)));
                        } else {
                            r = Z3_mk_ite(smt_solver.ctx, byte, r,
                                          smt_new_const(k, SIZE(op1)));
                        }
                    }
                }
                ABORT("Not yet implemented");
            }
            break;
        }
        //
        case CTZ: {
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
#if VERBOSE
            printf("CTZ\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            for (size_t i = 0; i < SIZE(op1); i++) {
                Z3_ast byte = Z3_mk_extract(smt_solver.ctx, SIZE(op1) - 1 - i,
                                            SIZE(op1) - 1 - i, op1);
                byte        = optimize_z3_query(byte);

                size_t k = SIZE(op1) - i - 1;
                if (is_zero_const(byte)) {
                    if (i == 0) {
                        r = smt_new_const(k + 1, SIZE(op1));
                    }
                } else {
                    byte = Z3_mk_eq(smt_solver.ctx, byte, smt_new_const(0, 1));
                    byte = optimize_z3_query(byte);
                    if (i == 0) {
                        r = Z3_mk_ite(smt_solver.ctx, byte,
                                      smt_new_const(k + 1, SIZE(op1)),
                                      smt_new_const(k, SIZE(op1)));
                    } else {
                        r = Z3_mk_ite(smt_solver.ctx, byte, r,
                                      smt_new_const(k, SIZE(op1)));
                    }
                    r = optimize_z3_query(r);
                }
            }
            if (op1 != op2) {
                Z3_ast c =
                    Z3_mk_eq(smt_solver.ctx, op1, smt_new_const(0, SIZE(op1)));
                c = optimize_z3_query(c);
                r = Z3_mk_ite(smt_solver.ctx, c, op2, r);
            }
            break;
        }
        //
        case BSWAP: {
            op1  = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            size = CONST(query->op2);
#if VERBOSE
            printf("BSWAP: size=%lu\n", size);
            smt_print_ast_sort(op1);
#endif
            size = size == 0 ? sizeof(uint64_t) : size;
            r    = NULL;
            for (size_t i = 0; i < size; i++) {
                Z3_ast e_byte =
                    Z3_mk_extract(smt_solver.ctx, (8 * (size - i)) - 1,
                                  8 * (size - i - 1), op1);
                e_byte = optimize_z3_query(e_byte);
                if (r == NULL) {
                    r = e_byte;
                } else {
                    r = Z3_mk_concat(smt_solver.ctx, e_byte, r);
                }
            }
            break;
        }
        //
        case NAND: {
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0,
                                  &op1_inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0,
                                  &op2_inputs);
            smt_bv_resize(&op1, &op2, CONST(query->op3));
#if VERBOSE
            printf("NAND\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvnand(smt_solver.ctx, op1, op2);
            break;
        }
        // x86 specific
        case RCL:
        case CMP_EQ:
        case CMP_GT:
        case CMP_GE:
        case CMP_LT:
        case CMP_LE:
        case PMOVMSKB:
        case MIN:
        case MAX:
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
        case EFLAGS_ALL_ADOX:
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
            r = smt_query_i386_to_z3(smt_solver.ctx, query, is_const_value,
                                     width, &op1_inputs);
            break;

        default:
            print_expr(query);
            ABORT("Unknown expr opkind: %s", opkind_to_str(query->opkind));
    }

        // printf("%s\n", Z3_ast_to_string(smt_solver.ctx, r));
#if 1
    if (debug_translation) {
        printf("PRE OPTIMIZE: %s\n", opkind_to_str(query->opkind));
        print_z3_ast(r);
    }
#endif

#if DEBUG_EXPR_OPT
    // printf("\nOPT CHECK BEFORE\n");
    Z3_ast orig_r = r;
#endif

    // printf("PRE OPTIMIZE: %s\n", opkind_to_str(query->opkind));
    r = optimize_z3_query(r);
    // printf("POST OPTIMIZE\n");
    // smt_print_ast_sort(r);
    // printf("END opkind: %s\n", opkind_to_str(query->opkind));

#if DEBUG_EXPR_OPT
    if (r != orig_r) { // && debug_translation
#if 0
        if (SIZE(r) != SIZE(orig_r)) {
            printf("OPT CHECK: size=%u size=%u\n", SIZE(orig_r), SIZE(r));
            printf("BEFORE:\n");
            print_z3_ast(orig_r);
            printf("AFTER:\n");
            print_z3_ast(r);
            ABORT();
        }

        if (SIZE(orig_r) <= 64) {
            for (size_t i = 0; i < testcase.size; i++) {
                eval_data[i] = testcase.data[i];
            }

            uintptr_t before_value = conc_query_eval_value(smt_solver.ctx, orig_r, eval_data,
                                                symbols_sizes, symbols_count);

            for (size_t i = 0; i < testcase.size; i++) {
                eval_data[i] = testcase.data[i];
            }

            uintptr_t after_value = conc_query_eval_value(smt_solver.ctx, r, eval_data,
                                                symbols_sizes, symbols_count);

            if (before_value == after_value) {
                // printf("OPT CHECK: expected=%lx solution=%lx\n", before_value, after_value);
            } else {
                printf("OPT CHECK: expected=%lx solution=%lx\n", before_value, after_value);
                printf("BEFORE:\n");
                print_z3_ast(orig_r);
                printf("AFTER:\n");
                print_z3_ast(r);
                ABORT();
            }
        } else {
            // ToDo: fallback to Z3
        }
#endif
        Z3_solver solver = smt_new_solver();
        Z3_ast    c      = Z3_mk_eq(smt_solver.ctx, r, orig_r);
        Z3_solver_assert(smt_solver.ctx, solver, Z3_mk_not(smt_solver.ctx, c));
        Z3_lbool res = Z3_solver_check(smt_solver.ctx, solver);
        if (res == Z3_L_TRUE) {
            printf("UNSAFE OPT\n");
            printf("BEFORE:\n");
            print_z3_ast(orig_r);
            printf("AFTER:\n");
            print_z3_ast(r);
            ABORT();
        }
        smt_del_solver(solver);
    }
#endif

#if 1
    if (debug_translation) {
        printf("POST OPTIMIZE %s\n", opkind_to_str(query->opkind));
        print_z3_ast(r);
    }
#endif
#if 0
    int r_size = IS_BOOL(r) ? 1 : SIZE(r);
    r = optimize_z3_query_division(r);
    if (!IS_BOOL(r) && SIZE(r) != r_size) {
        ABORT();
    }
#endif
    ce         = malloc(sizeof(CachedExpr));
    ce->expr   = r;
    *inputs    = merge_inputs(op1_inputs, op2_inputs);
    ce->inputs = *inputs;
    g_hash_table_insert(z3_expr_cache, (gpointer)query, (gpointer)ce);
    return r;
}

static void smt_stats(Z3_solver solver)
{
    Z3_stats stats = Z3_solver_get_statistics(smt_solver.ctx, solver);
    Z3_stats_inc_ref(smt_solver.ctx, stats);
    const char* s_stats = Z3_stats_to_string(smt_solver.ctx, stats);
    printf("%s\n", s_stats);
    Z3_stats_dec_ref(smt_solver.ctx, stats);

    if (smt_solver.sat_count > 0) {
        printf("SAT queries: count=%lu avg=%lu\n", smt_solver.sat_count,
               (smt_solver.sat_time / smt_solver.sat_count));
    }
    if (smt_solver.unsat_count > 0) {
        printf("UNSAT queries: count=%lu avg=%lu\n", smt_solver.unsat_count,
               (smt_solver.unsat_time / smt_solver.unsat_count));
    }
    if (smt_solver.unknown_count > 0) {
        printf("UNKNOWN queries: count=%lu avg=%lu\n", smt_solver.unknown_count,
               (smt_solver.unknown_time / smt_solver.unknown_count));
    }
}

int generate_matching_pattern(Z3_ast e)
{
    uint64_t value;
    Z3_context  ctx  = smt_solver.ctx;
    Z3_ast_kind kind = Z3_get_ast_kind(ctx, e);
    if (kind != Z3_APP_AST) {
        if (is_const(e, &value)) {
            printf(" 'c', 0x%lx,", value);
            return 1;
        } else {
            return 0;
        }
    }

    Z3_decl_kind decl_kind    = OP(e);
    unsigned     num_operands = N_ARGS(e);

    if (decl_kind == Z3_OP_CONCAT) {
        for (size_t i = 0; i < num_operands; i++) {
            Z3_ast child = ARG(e, i);
            Z3_ast_kind child_kind = Z3_get_ast_kind(ctx, child);
            if (child_kind == Z3_APP_AST && OP(child) == Z3_OP_UNINTERPRETED) {
                printf("'i', ");
                return 1;
            }
        }
    }

    printf("'a', %d, %d, ", IS_BOOL(e) ? 1 : SIZE(e), decl_kind);

    switch(decl_kind) {
        case Z3_OP_EXTRACT:
            printf("'p', %d, ", PARAM1(e));
            printf("'p', %d, ", PARAM2(e));
            break;
        case Z3_OP_ZERO_EXT:
        case Z3_OP_SIGN_EXT:
            printf("'p', %d, ", PARAM1(e));
            break;
        default:
            break;
    }

    for (size_t i = 0; i < num_operands; i++) {
        int r = generate_matching_pattern(ARG(e, i));
        if (!r) {
            return 0;
        }
    }

    return 1;
}

static void smt_branch_query(Query* q)
{
#if 0
    smt_stats(smt_solver.solver);
#endif

#if 0
    if (GET_QUERY_IDX(q) >= 13668) {
        debug_translation = 1;
    }
#endif
#if 0
    printf("\nBranch at 0x%lx (id=%lu, taken=%u)\n", q->address,
                   GET_QUERY_IDX(q), (uint16_t)q->args64);
    print_expr(q->query);
#endif
    // SAYF("Translating query %lu to Z3...\n", GET_QUERY_IDX(q));
    GHashTable* inputs   = NULL;
    Z3_ast      z3_query = smt_query_to_z3_wrapper(q->query, 0, 0, &inputs);
    z3_ast_exprs[GET_QUERY_IDX(q)] = z3_query;
    // SAYF("DONE: Translating query to Z3\n");
#if 1
    if (OP(z3_query) == Z3_OP_FALSE) {
        print_z3_ast(z3_query);
        print_expr(q->query);
        ABORT();
    }
#endif
#if 0
    debug_translation = 0;
#endif
    if (!inputs) {
        return;
    }

#if 0
    Z3_ast z3_query_2 = Z3_simplify(smt_solver.ctx, z3_query);
    print_z3_original(z3_query_2);
#endif

#if 0
    get_inputs_expr(z3_query);
#endif
    Z3_ast z3_neg_query = Z3_mk_not(smt_solver.ctx, z3_query); // invert branch

#if 0
    Z3_set_ast_print_mode(smt_solver.ctx, Z3_PRINT_LOW_LEVEL);
    const char* z3_query_str = Z3_ast_to_string(smt_solver.ctx, z3_query);
    SAYF("%s", z3_query_str);
#endif
#if 0
    // if (GET_QUERY_IDX(q) == 54) {
    print_z3_ast(z3_neg_query);
    // ABORT();
    // }
#endif

#if 0
    print_z3_ast(ARG1(ARG1(z3_query)));
    printf("uint64_t pattern[]= { ");
    int r = generate_matching_pattern(ARG1(ARG1(z3_query)));
    printf(" };\n");
    if (!r) {
        printf("Pattern is INVALID\n");
    }
#endif

    uint8_t has_real_inputs = 0;

    GHashTableIter iter;
    gpointer       key, value;
    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        if ((uintptr_t)key < MAX_INPUT_SIZE) {
            has_real_inputs = 1;
            break;
        } else if (!concretized_sloads[(uintptr_t)key]) {
            has_real_inputs = 1;
            break;
        }
    }
#if 0
    for (size_t i = 0; i < symbols_count; i++) {
        assert(symbols_sizes[i]);
        printf("Index=%lu size=%u\n", i, symbols_sizes[i]);
    }
#endif
    if (has_real_inputs) {
#if BRANCH_COVERAGE == QSYM
        if (is_interesting_branch(q->address, q->args8.arg0)) {
#elif BRANCH_COVERAGE == AFL
        if (is_interesting_branch(q->address, q->args64)) {
#elif BRANCH_COVERAGE == FUZZOLIC
        if (is_interesting_branch(q->args16.index, q->args16.count,
                                  q->args16.index_inv, q->args16.count_inv)) {
#endif
            printf("\nBranch at 0x%lx (id=%lu, taken=%u)\n", q->address,
                   GET_QUERY_IDX(q), (uint16_t)q->args64);
#if USE_FUZZY_SOLVER
            Z3_ast deps;
            update_and_add_deps_to_solver(inputs, GET_QUERY_IDX(q), NULL,
                                          &deps);
            // print_z3_ast(deps);
            Z3_ast         args[]      = {z3_neg_query, deps};
            Z3_ast         fuzzy_query = Z3_mk_and(smt_solver.ctx, 2, args);
            const uint8_t* proof;
            size_t         proof_size;

            // fuzzy_query = Z3_simplify(smt_solver.ctx, fuzzy_query);

            // print_z3_ast(fuzzy_query);
            // print_z3_ast(z3_neg_query);
            // print_z3_ast(Z3_simplify(smt_solver.ctx, z3_neg_query));
#if 0
            if (GET_QUERY_IDX(q) == 8816) {
                if (cached_solver == NULL) {
                    cached_solver = smt_new_solver();
                }
                Z3_solver solver = cached_solver;
                Z3_solver_assert(
                        smt_solver.ctx, solver,
                        fuzzy_query);
                smt_dump_solver(solver, GET_QUERY_IDX(q));
                Z3_solver_reset(smt_solver.ctx, solver);
            }
#endif
            printf("Running a query...\n");
            conc_eval_time  = 0;
            conc_eval_count = 0;
            struct timespec start, end;
            get_time(&start);
            int r = z3fuzz_query_check_light(&smt_solver.fuzzy_ctx, fuzzy_query,
                                             z3_neg_query, &proof, &proof_size);
            get_time(&end);
            printf("Elapsed: %lu us\n", get_diff_time_microsec(&start, &end));
            if (r) {
                printf("Query is SAT\n");
                smt_dump_testcase(proof, testcase.size, 1, GET_QUERY_IDX(q), 0);
            } else {
                if (conc_eval_count > 0) {
                    printf("Query is non-SAT: avg_conc_eval=%lu count=%lu\n",
                           conc_eval_time / conc_eval_count, conc_eval_count);
                }
                unsat_time += get_diff_time_microsec(&start, &end);
                unsat_count += 1;
                printf("UNSAT: sum=%lu count=%lu\n", unsat_time, unsat_count);
                if (config.optimistic_solving) {
                    r = z3fuzz_get_optimistic_sol(&smt_solver.fuzzy_ctx, &proof,
                                                  &proof_size);
                    if (r) {
                        printf("Query is SAT [OPTIMISTIC]\n");
                        smt_dump_testcase(proof, testcase.size, 1,
                                          GET_QUERY_IDX(q), 666);
                    }
                }
            }
            printf(" [INFO] Branch interesting: addr=0x%lx taken=%u sat=%d\n",
                   q->address, (uint16_t)q->args64, r);
#else
            Z3_solver solver = smt_new_solver();
#if 0
            if (GET_QUERY_IDX(q) == 275) {
                // print_expr(q->query);
                print_z3_ast(z3_neg_query);
                debug_translation = 1;
            }
#endif
            // print_z3_ast(z3_neg_query);
            // print_z3_original(z3_neg_query);
            // print_expr(q->query);

            update_and_add_deps_to_solver(inputs, GET_QUERY_IDX(q), solver,
                                          NULL);

#if 0
            Z3_lbool res = Z3_solver_check(smt_solver.ctx, solver);
            if (res != Z3_L_TRUE) {
                if (res == Z3_L_FALSE) {
                    ABORT();
                }
            }
#endif
            Z3_solver_assert(smt_solver.ctx, solver, z3_neg_query);
            // Z3_simplify(smt_solver.ctx, z3_neg_query));
            // SAYF("Running a query...\n");
#if 0
            smt_dump_solver_to_file(solver, "/home/ercoppa/Desktop/code/fuzzolic/temp.query");
            int is_sat = smt_run_from_file("/home/ercoppa/Desktop/code/fuzzolic/temp.query");
#endif
#if 0
            int is_sat = smt_run_from_string(solver, GET_QUERY_IDX(q));
#endif
#if !DISABLE_SMT
            int is_sat = smt_query_check(solver, GET_QUERY_IDX(q), 0);
            if (config.optimistic_solving && !is_sat) {
                Z3_solver_reset(smt_solver.ctx, solver);
                Z3_solver_assert(smt_solver.ctx, solver, z3_neg_query);
                smt_query_check(solver, GET_QUERY_IDX(q), 1);
            }
            printf(" [INFO] Branch interesting: addr=0x%lx taken=%u sat=%d\n",
                   q->address, (uint16_t)q->args64, is_sat);

#endif
#if 0
            if (q->address == 0x40013b38da) {
                smt_dump_solver(solver, GET_QUERY_IDX(q));
            }
#endif

            smt_del_solver(solver);
#endif
        } else {
#if 0
            printf("Branch (addr=%lx id=%lu) is not interesting. Skipping it.\n", 
                    q->address, GET_QUERY_IDX(q));
#endif
            update_and_add_deps_to_solver(inputs, GET_QUERY_IDX(q), NULL, NULL);
        }

#if 0
        {
            if (cached_solver == NULL) {
                cached_solver = smt_new_solver();
            }
            Z3_solver solver = cached_solver;

            add_deps_to_solver(inputs, solver);
            Z3_lbool res = Z3_solver_check(smt_solver.ctx, solver);
            if (res != Z3_L_TRUE) {
                if (res == Z3_L_FALSE) {
                    print_z3_ast(z3_query);
                    print_expr(q->query);
                    ABORT();
                }
            }
            Z3_solver_reset(smt_solver.ctx, solver);
        }
#endif
#if 0
        Z3_ast pi = get_deps(inputs);
        for (size_t i = 0; i < testcase.size; i++) {
            eval_data[i] = testcase.data[i];
        }
        uintptr_t solution = conc_query_eval_value(smt_solver.ctx, pi, eval_data,
                                            symbols_sizes, symbols_count);

        if (solution == 0) {
            print_z3_ast(z3_query);
            print_expr(q->query);
            ABORT();
        }
#endif
    } else {
        // printf("No real inputs in branch condition. Skipping it.\n");
    }
#if 0
    if (GET_QUERY_IDX(q) == 2218)
        ABORT();
#endif
#if USE_FUZZY_SOLVER
    z3fuzz_notify_constraint(&smt_solver.fuzzy_ctx, z3_query);
#endif
}

static int get_eval_uint64(Z3_model m, Z3_ast e, uintptr_t* value)
{
    Z3_ast solution;

    Z3_bool successfulEval =
        Z3_model_eval(smt_solver.ctx, m, e, Z3_FALSE, &solution);
    assert(successfulEval && "Failed to evaluate model");

    if (Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_NUMERAL_AST) {
        Z3_get_numeral_int64(smt_solver.ctx, solution, (int64_t*)value);
        return 1;
    }

    assert(Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_APP_AST &&
           "Evaluated expression has wrong sort");

    Z3_lbool rf = Z3_get_bool_value(smt_solver.ctx, solution);
    if (rf == Z3_L_TRUE) {
        return 1;
    } else if (rf == Z3_L_FALSE) {
        return 0;
    } else {
        ABORT("Should not happen.");
    }
}

uint64_t conc_query_eval_value(Z3_context ctx, Z3_ast query, uint64_t* data,
                               uint8_t* _symbols_sizes, size_t size)
{
    if (!query) {
        return 1;
    }

    struct timespec start, end;
    get_time(&start);

    uintptr_t value;
    GSList*   el           = sloads_exprs;
    size_t    n_data_bytes = testcase.size;
    while (el) {

        SLoad* sl = (SLoad*)el->data;
        el        = el->next;

        size_t i     = sl->index;
        n_data_bytes = i + 2;
        // printf("Analyzing sloads_%lu (%lu) [%lu]\n",
        // reverse_scale_sload_index(i), i, i - testcase.size);
        // printf("n_data_bytes=%lu size=%lu\n", n_data_bytes, size);
        assert(n_data_bytes <= size);

        Z3_ast e = sl->expr;

        assert(i < MAX_INPUTS_EXPRS);

        // printf("Analyzing sloads_%lu (%lu)\n", reverse_scale_sload_index(i),
        // i);

        if (concretized_sloads[i]) {
            data[i] = CONST(e);
            assert(i < size);
            // printf("s_load_%lu: %lx\n", i, CONST(e));
            assert(0);
        } else {

            assert(e && OP(e) == Z3_OP_AND);
            // printf("Getting concrete value of s_load_%lu\n", i);

            Z3_ast s    = ARG1(ARG2(e));
            Z3_ast addr = ARG2(ARG2(e));

            Z3_ast s_expr  = ARG1(ARG1(e));
            Z3_ast s_value = ARG2(ARG1(e));

            Z3_ast or_addr = ARG3(e);

            // First we need to get solution for addr:
            // this will get us an intepretation for s
            // Then we get solution for s_expr, giving
            // us an interpretation for s_value

            value = Z3_custom_eval(smt_solver.ctx, addr, data, symbols_sizes,
                                   n_data_bytes);
            data[i + 1] = value;

            value = Z3_custom_eval(smt_solver.ctx, s_value, data, symbols_sizes,
                                   n_data_bytes);
            data[i] = value;
            assert(i < size);

            // printf("s_load_%lu: %lx\n", i, value);
        }
    }

#if 0
    smt_dump_testcase(data, size, 8, 0, 0);

    Z3_solver solver = smt_new_solver();
    Z3_solver_assert(smt_solver.ctx, solver, query);
    smt_dump_solver(solver, 0);
    smt_del_solver(solver);
#endif
    // printf("conc eval new:\n");
    uint64_t r = Z3_custom_eval(smt_solver.ctx, query, data, symbols_sizes,
                                n_data_bytes);
    // printf("conc eval new: %lu\n", r);

    get_time(&end);
    conc_eval_time += get_diff_time_microsec(&start, &end);
    conc_eval_count += 1;

    return r;
}

#if 0
static Z3_model conc_query_eval_value_old(Z3_ast query, uintptr_t input_val,
                                      size_t input_index, uint8_t* data,
                                      size_t size)
{
    Z3_ast    solution;
    uintptr_t value, value2;

    // printf("Model m[%lu] = %lu\n", input_index, input_val);

    // build a model and assign an interpretation for the input symbol
    Z3_model z3_m = Z3_mk_model(smt_solver.ctx);
    for (size_t i = 0; i < size; i++) {
        Z3_sort sort = Z3_mk_bv_sort(smt_solver.ctx, 8);
        Z3_ast  e    = Z3_mk_unsigned_int64(
            smt_solver.ctx, input_index == i ? input_val : data[i], sort);
        Z3_symbol s = Z3_mk_int_symbol(smt_solver.ctx, i);
        Z3_func_decl decl = Z3_mk_func_decl(smt_solver.ctx, s, 0, NULL, sort);
        Z3_add_const_interp(smt_solver.ctx, z3_m, decl, e);
    }

    if (!query) {
        Z3_model_inc_ref(smt_solver.ctx, z3_m);
        return z3_m;
    }

    GSList* el = sloads_exprs;
    while (el) {

        SLoad* sl = (SLoad*)el->data;
        el        = el->next;

        size_t i = sl->index;
        Z3_ast e = sl->expr;

        // printf("Analyzing sloads_%lu (%lu)\n", reverse_scale_sload_index(i), i);
        // print_z3_ast(e);

        Z3_sort sort;
        if (concretized_sloads[i]) {
            sort = Z3_mk_bv_sort(smt_solver.ctx, 64);
            e = Z3_mk_unsigned_int64(smt_solver.ctx, CONST(e), sort);
            // printf("s_load_%lu value is %lu\n", i, value);
            // printf("s_load_%lu: %lx\n", i, CONST(e));
        } else {

            assert(e && OP(e) == Z3_OP_AND);
            // printf("Getting concrete value of s_load_%lu\n", i);

            Z3_ast s    = ARG1(ARG2(e));
            Z3_ast addr = ARG2(ARG2(e));

            Z3_ast s_expr  = ARG1(ARG1(e));
            Z3_ast s_value = ARG2(ARG1(e));

            Z3_ast or_addr = ARG3(e);

            // First we need to get solution for addr:
            // this will get us an intepretation for s
            // Then we get solution for s_expr, giving
            // us an interpretation for s_value

            int r = get_eval_uint64(z3_m, addr, &value);
            if (!r) {
                return NULL;
            }

            Z3_symbol symbol = Z3_mk_int_symbol(smt_solver.ctx, i + 1);
            sort = Z3_get_sort(smt_solver.ctx, s);
            Z3_func_decl decl =
                Z3_mk_func_decl(smt_solver.ctx, symbol, 0, NULL, sort);
            Z3_ast v = Z3_mk_unsigned_int64(smt_solver.ctx, value, sort);
            Z3_add_const_interp(smt_solver.ctx, z3_m, decl, v);

            r = get_eval_uint64(z3_m, s_value, &value);
            if (!r) {
                return NULL;
            }

            //printf("s_load_%lu: %lx\n", i, value);

            sort = Z3_get_sort(smt_solver.ctx, s_value);
            e    = Z3_mk_unsigned_int64(smt_solver.ctx, value, sort);
        }

        Z3_symbol s = Z3_mk_int_symbol(smt_solver.ctx, i);
        Z3_func_decl decl = Z3_mk_func_decl(smt_solver.ctx, s, 0, NULL, sort);
        Z3_add_const_interp(smt_solver.ctx, z3_m, decl, e);
    }

    int r = get_eval_uint64(z3_m, query, &value);
    //printf("conc eval old: %d\n", r);
    if (r) {
        Z3_model_inc_ref(smt_solver.ctx, z3_m);
        return z3_m;
    } else {
        return NULL;
    }
}

static int fuzz_query_eval_old(GHashTable* inputs, Z3_ast expr,
                           GHashTable* solutions, uintptr_t dump_idx)
{
    GHashTableIter iter;
    gpointer       key, value;

    // copy inputs since get_deps will add other inputs
    // that we do not want to fuzz
    GHashTable* inputs_copy = g_hash_table_new(NULL, NULL);
    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        g_hash_table_add(inputs_copy, key);
    }

    Z3_ast query = get_deps(inputs);

    g_hash_table_iter_init(&iter, inputs_copy);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        size_t index = (size_t)key;

        if (index >= testcase.size) {
            // printf("Not fuzzing input byte: %lu\n", index);
            continue;
        }

        printf("Fuzzing input byte: %lu\n", index);
        uintptr_t conc_value = testcase.data[index];

        uint8_t fuzz_values[] = {
            0, 1, 127, 255, testcase.data[index] - 1, testcase.data[index] + 1};
        for (ssize_t i = 0; i < sizeof(fuzz_values) / sizeof(uint8_t); i++) {
            Z3_model m = conc_query_eval_value_old(query, fuzz_values[i], index,
                                               testcase.data, testcase.size);
            //printf("Done eval old\n");
            if (m) {
                uintptr_t solution = smt_query_eval_uint64(m, expr);

                if (g_hash_table_contains(solutions, (gpointer)solution) !=
                    TRUE) {
                    printf("Found a valid solution: %lx\n", solution);
                    g_hash_table_add(solutions, (gpointer)solution);
                }
                Z3_model_dec_ref(smt_solver.ctx, m);
            }
        }
    }

    g_hash_table_destroy(inputs_copy);
    return g_hash_table_size(solutions) > 1;
}
#endif

static int smt_all_solutions(GHashTable* inputs, Z3_ast z3_query,
                           GHashTable* solutions, uintptr_t solution)
{
    int       count    = 0;
    Z3_solver solver   = smt_new_solver();
    add_deps_to_solver(inputs, solver);
    while (count < 256) {
        assert(solution);
        Z3_ast c = Z3_mk_eq(smt_solver.ctx, z3_query,
                            smt_new_const(solution, sizeof(uintptr_t) * 8));
        c        = Z3_mk_not(smt_solver.ctx, c);
        Z3_solver_assert(smt_solver.ctx, solver, c);
        int r = smt_query_check_eval_uint64(solver, 0, z3_query,
                                            &solution, 0);
        if (!r)
            break;
        // SAYF("New slice target is %lx\n", solution);
        count += 1;
        g_hash_table_add(solutions, (gpointer) solution);
    }
    smt_del_solver(solver);
    return g_hash_table_size(solutions) > 1;
}

static int fuzz_query_eval(GHashTable* inputs, Z3_ast expr,
                           GHashTable* solutions, uintptr_t dump_idx,
                           uintptr_t start, uintptr_t end)
{
    GHashTableIter iter;
    gpointer       key, value;

    Z3_ast query = get_deps(inputs);
    // print_z3_ast(query);

    for (size_t i = 0; i < testcase.size; i++) {
        eval_data[i] = testcase.data[i];
    }

    uint8_t full_values[256];
    for (size_t i = 0; i < sizeof(full_values) / sizeof(uint8_t); i++) {
        full_values[i] = i;
    }

    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        size_t index = CONST(key);

        if (index >= testcase.size) {
            // printf("Not fuzzing input byte: %lu\n", index);
            continue;
        }

        // printf("Fuzzing input byte: %lu\n", index);

        uint8_t fuzz_values[] = {
            0, 1, 127, 255, testcase.data[index] - 1, testcase.data[index] + 1};

        uint8_t* values = NULL;
        size_t values_count = 0;
        if (g_hash_table_contains(concretized_bytes, key) == TRUE) {
            // printf("Byte index is overconstrained: %lu\n", index);
            values = fuzz_values;
            values_count = sizeof(fuzz_values) / sizeof(uint8_t);
        } else {
            values = full_values;
            values_count = sizeof(full_values) / sizeof(uint8_t);
        }

        // printf("Fuzzing input byte: %lu attempts=%lu\n", index, values_count);

        size_t success = 0;
        for (ssize_t i = 0; i < values_count; i++) {

            // printf("attempt=%lu count=%lu success=%lu\n", i, values_count, success);
            if (values_count > 16 && i > 3 && success == 0) {
                // printf("Bail out\n");
                break;
            }

            // printf("Testing input[%lu] = %u\n", index, values[i]);

            uint8_t original_value = eval_data[index];
            eval_data[index]       = values[i];

            int r = conc_query_eval_value(smt_solver.ctx, query, eval_data,
                                          symbols_sizes, symbols_count);
            if (r) {
                uintptr_t solution =
                    Z3_custom_eval(smt_solver.ctx, expr, eval_data,
                                   symbols_sizes, symbols_count);
                if (g_hash_table_contains(solutions, (gpointer)solution) !=
                    TRUE) {

                    success += 1;
#if 0
                    printf("Found a valid solution %lx using fuzz value %u at "
                           "index %ld\n",
                           solution, fuzz_values[i], index);
#endif
                    g_hash_table_add(solutions, (gpointer)solution);
                    // printf("Solution: %lx\n", solution);
                    if (dump_idx && ((start == 0 && end == 0) || solution < start || solution > end)) {
#if 0
                        if (!(start == 0 && end == 0)) {
                            printf("Boundaries: [%lu, %lu] - solution: %lu\n", start, end, solution);
                        }
#endif
                        smt_dump_testcase((uint8_t*)eval_data, testcase.size, 8,
                                          dump_idx,
                                          g_hash_table_size(solutions) - 1);
                    }
                }
            }

            eval_data[index] = original_value;
        }
    }

    return g_hash_table_size(solutions) > 1;
}

static uintptr_t get_value_from_slice_array(Expr** slices_addrs,
                                            size_t slice_count, uintptr_t addr,
                                            size_t size, uint8_t* out_of_bounds)
{
    *out_of_bounds = 0;
    // printf("Fetching value for addr 0x%lx\n", addr);
    for (size_t i = 0; i < slice_count; i++) {
        Expr*     slice     = slices_addrs[i];
        uintptr_t base_addr = CONST(slice->op1);
        // printf("Base addr for slice %lu is %lx\n", i, base_addr);
        // assert(addr >= base_addr);
        if (addr < base_addr) {
            printf("ERROR: out of bounds slice access: addr=%lu slice_id=%lu "
                   "base_addr=%lu\n",
                   addr, i, base_addr);
            *out_of_bounds = 1;
            return 0;
        }
        if (base_addr + SLICE_SIZE >= addr + size) {
            size_t offset = addr - base_addr;
            assert(offset < SLICE_SIZE);
            uint8_t* raw_data = (uint8_t*)&(slice->op2);
            raw_data += offset;
            switch (size) {
                case 1: {
                    uint8_t* data = raw_data;
                    return *data;
                }

                case 2: {
                    uint16_t* data = (uint16_t*)raw_data;
                    return *data;
                }

                case 4: {
                    uint32_t* data = (uint32_t*)raw_data;
                    return *data;
                }

                case 8: {
                    uint64_t* data = (uint64_t*)raw_data;
                    return *data;
                }

                default:
                    ABORT("Invalid slice size value.");
            }
        }
    }
    printf("ERROR: out of bounds slice access: addr=%lu\n", addr);
    *out_of_bounds = 1;
    return 0;
}

static Z3_ast get_input_from_slice_array(uintptr_t addr, size_t size,
                                            uintptr_t start, uintptr_t end,
                                            uintptr_t offset,
                                            GHashTable* slice_inputs,
                                            uint8_t* out_of_bounds)
{
    if (addr < start || addr > end) {
        printf("ERROR: out of bounds input slice access: addr=%lx\n", addr);
        *out_of_bounds = 1;
        return NULL;
    }

    uintptr_t index = (addr - start) + offset;
    *out_of_bounds = 0;
    Z3_ast z3_expr = NULL;
    for (size_t i = 0; i < size; i++) {
        g_hash_table_add(slice_inputs, (gpointer)(index + i));
        Z3_ast byte = input_exprs[index + i];
        if (byte == NULL) {
            byte = smt_new_symbol_int(index + i, 8, NULL);
            input_exprs[index + i] = byte;
        }
        if (z3_expr == NULL) {
            z3_expr = byte;
        } else {
            z3_expr = Z3_mk_concat(smt_solver.ctx, z3_expr, byte);
        }
    }
    return z3_expr;
}

static void smt_slice_query(Query* q)
{
    Expr*     addr_expr = q->query->op1;
    uintptr_t addr_conc = CONST(q->query->op2);
    uintptr_t s_load_id = CONST(q->query->op3);

    // symbolic input expression
    Expr* s_load = (q->query + 1);
    assert(s_load->opkind == IS_SYMBOLIC);
    assert(CONST(s_load->op1) == s_load_id);
    uintptr_t s_load_size = CONST(s_load->op2);
    assert(s_load_size > 0);

    uintptr_t s_load_value = 0;
    uintptr_t s_load_input_offset = 0;

    if (q->query->opkind == MEMORY_SLICE_ACCESS) {
        s_load_value = CONST(s_load->op3);
        printf("\nSlice access: id=%lu load_id=%lu (%lu) conc_addr=0x%lx size=%lu "
            "value=0x%lx.\n",
            GET_QUERY_IDX(q), s_load_id, scale_sload_index(s_load_id), addr_conc,
            s_load_size, s_load_value);
    } else if (q->query->opkind == MEMORY_INPUT_SLICE_ACCESS) {
        // printf("Expr ID: %lu\n", GET_EXPR_IDX(s_load));
        s_load_input_offset = CONST(s_load->op3);
        printf("\nSlice input access: id=%lu load_id=%lu (%lu) conc_addr=0x%lx size=%lu input_offset=%lu.\n",
            GET_QUERY_IDX(q), s_load_id, scale_sload_index(s_load_id), addr_conc,
            s_load_size, s_load_input_offset);
    } else {
        ABORT();
    }
#if 0
    if (GET_QUERY_IDX(q) == 448) {
        debug_translation = 1;
    }
#endif
    Z3_ast s_expr = smt_query_to_z3_wrapper(s_load, 0, 0, NULL);
#if 0
    get_inputs_expr(s_expr);
#endif

    GHashTable* inputs  = NULL;
    Z3_ast      z3_addr = smt_query_to_z3_wrapper(addr_expr, 0, 0, &inputs);

    // print_expr(addr_expr);
    // print_z3_ast(z3_addr);

#if 0
    get_inputs_expr(z3_addr);
#endif

#if 0
    GHashTableIter iter;
    gpointer       key, value;
    GHashTable* inputs_copy = g_hash_table_new(NULL, NULL);
    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        g_hash_table_add(inputs_copy, key);
    }
#endif

    uintptr_t slice_start = 0, slice_end = 0;
    uintptr_t offset_start = 0;

    // recover slice pointers
    size_t slices_count                     = 0;
    Expr*  slices_addrs[MAX_NUM_SLICES + 1] = {0};
    Expr*  slice                            = (q->query + 2);

    if (q->query->opkind == MEMORY_SLICE_ACCESS) {
        while (slice->opkind == MEMORY_SLICE) {
            assert(CONST(slice->op2) == s_load_id);
            slices_addrs[slices_count] = slice->op1;
            slices_count += 1;
            // printf("Slice at %p.\n", slice->op1);
            assert(slices_count <= MAX_NUM_SLICES);
            slice += 1;
        }
        assert(slices_count > 0);

        if (config.address_reasoning) {
            for (size_t i = 0; i < slices_count; i++) {
                uintptr_t ss = CONST(slices_addrs[i]->op1);
                uintptr_t se = CONST(slices_addrs[i]->op1) + SLICE_SIZE - s_load_size;
                if (slice_start == 0 || slice_start > ss) {
                    slice_start = ss;
                }
                if (slice_end == 0 || slice_end < se) {
                    slice_end = se;
                }
            }
        }

    } else if (q->query->opkind == MEMORY_INPUT_SLICE_ACCESS) {
        Expr* input_slice = (q->query + 2);
        assert(input_slice->opkind == INPUT_SLICE);
        slice_start = CONST(input_slice->op1);
        slice_end = CONST(input_slice->op2);
        offset_start = CONST(input_slice->op3);
    }

    GHashTable* conc_addrs = g_hash_table_new(NULL, NULL);
    g_hash_table_add(conc_addrs, (gpointer)addr_conc);
    int r = 0;
    if (config.memory_slice_reasoning && inputs) {
        struct timespec start, end;
        get_time(&start);
#if FUZZ_SLICE_ADDRESS
        r = fuzz_query_eval(inputs, z3_addr, conc_addrs,
                config.address_reasoning ? GET_QUERY_IDX(q) : 0,
                slice_start, slice_end);
#else
        r = smt_all_solutions(inputs, z3_addr,conc_addrs, addr_conc);
#endif
        get_time(&end);
        uint64_t elapsed_microsecs = get_diff_time_microsec(&start, &end);
        printf("Slice reasoning time: %lu us\n", elapsed_microsecs);
        smt_solver.slice_reasoning_time += elapsed_microsecs;
    }
#if 0
    GHashTable* conc_addrs2 = g_hash_table_new(NULL, NULL);
    g_hash_table_add(conc_addrs2, (gpointer)addr_conc);
    int r2 = fuzz_query_eval_old(inputs_copy, z3_addr, conc_addrs2, 0);

    assert(r == r2);
#endif

    if (!r) {
        printf("Slice access has a single value. Concretizing it.\n");
        g_hash_table_remove(z3_expr_cache, (gpointer)s_load);
        if (q->query->opkind == MEMORY_SLICE_ACCESS) {
            concretized_sloads[scale_sload_index(s_load_id)] = 1;
        } else {
            uint8_t out_of_bounds;
            GHashTable* slice_inputs = g_hash_table_new(NULL, NULL);
            Z3_ast z3_expr = get_input_from_slice_array(addr_conc, s_load_size,
                                            slice_start, slice_end, offset_start,
                                            slice_inputs, &out_of_bounds);
            assert(out_of_bounds == 0);
            CachedExpr* ce  = malloc(sizeof(CachedExpr));
            ce->expr   = z3_expr;
            ce->inputs = slice_inputs;
            g_hash_table_insert(z3_expr_cache, (gpointer) s_load, (gpointer)ce);
            concretized_iloads[scale_sload_index(s_load_id)] = z3_expr;
        }
        // printf("Setting sloads_exprs for %lu (%lu)\n", s_load_id,
        // scale_sload_index(s_load_id));
#if 0
#if USE_FUZZY_SOLVER
        // printf("Assignment: %lu\n", scale_sload_index(s_load_id));
        z3fuzz_add_assignment(&smt_solver.fuzzy_ctx,
                              scale_sload_index(s_load_id),
                              smt_new_const(s_load_value, s_load_size * 8));
        z3fuzz_add_assignment(&smt_solver.fuzzy_ctx,
                              scale_sload_index(s_load_id) + 1,
                              smt_new_const(0, sizeof(uintptr_t) * 8));
#endif

        SLoad* s_load_obj = malloc(sizeof(SLoad));
        s_load_obj->index = scale_sload_index(s_load_id);
        s_load_obj->expr  = (Z3_ast)
            s_load_value; // smt_new_const(s_load_value, s_load_size * 8);
        sloads_exprs = g_slist_append(sloads_exprs, (gpointer)s_load_obj);
#endif
        symbols_sizes[scale_sload_index(s_load_id)]     = s_load_size * 8;
        symbols_sizes[scale_sload_index(s_load_id) + 1] = sizeof(uintptr_t) * 8;
        symbols_count += 2;
#if 0
        printf("symbols_sizes[%lu] = %lu %p\n", scale_sload_index(s_load_id), s_load_size * 8, symbols_sizes);
        printf("symbols_sizes[%lu] = %lu %p\n", scale_sload_index(s_load_id) + 1, sizeof(uintptr_t) * 8, symbols_sizes);

        for (size_t i = 0; i < symbols_count; i++) {
            assert(symbols_sizes[i]);
            printf("Index=%lu size=%u\n", i, symbols_sizes[i]);
        }
#endif

#if DEBUG_EXPR_OPT
        uintptr_t sol_addr = 0;
        if (is_const(z3_addr, &sol_addr) && sol_addr != addr_conc) {
            ABORT();
        }
#endif

        // concretize the address
        if (inputs) {
            Z3_ast c =
                Z3_mk_eq(smt_solver.ctx, z3_addr,
                         smt_new_const(addr_conc, sizeof(uintptr_t) * 8));

            z3_ast_exprs[GET_QUERY_IDX(q)] = c;
            update_and_add_deps_to_solver(inputs, GET_QUERY_IDX(q), NULL, NULL);

#if USE_FUZZY_SOLVER
            z3fuzz_notify_constraint(&smt_solver.fuzzy_ctx, c);
#endif
        }

        g_hash_table_destroy(conc_addrs);
        return;
    }
#if 0
    assert(g_hash_table_size(conc_addrs) == g_hash_table_size(conc_addrs2));
#endif
    printf("Slice access has multiple values: %d\n",
           g_hash_table_size(conc_addrs));

    Z3_ast s = z3_new_symbol_int(scale_sload_index(s_load_id) + 1,
                                 sizeof(uintptr_t) * 8);

    Z3_ast v = NULL;
    uint8_t is_out_of_slice_bounds;
    if (q->query->opkind == MEMORY_SLICE_ACCESS) {
        v = smt_new_const(s_load_value, s_load_size * 8);
    } else {
        v = get_input_from_slice_array(addr_conc, s_load_size,
                                        slice_start, slice_end, offset_start,
                                        inputs, &is_out_of_slice_bounds);
        // printf("addr=%lx start=%lx end=%lx\n", addr_conc, slice_start, slice_end);
        assert(is_out_of_slice_bounds == 0);
    }

    Z3_ast* or_args = malloc(sizeof(Z3_ast) * g_hash_table_size(conc_addrs));
    size_t  k       = 0;
    or_args[k++]    = Z3_mk_eq(smt_solver.ctx, s,
                            smt_new_const(addr_conc, sizeof(uintptr_t) * 8));
    GHashTableIter iter;
    gpointer       key, value;
    g_hash_table_iter_init(&iter, conc_addrs);
    int fetched_slice_values = 1;
    while (g_hash_table_iter_next(&iter, &key, &value)) {

        uintptr_t addr = (uintptr_t)key;
        if (addr == addr_conc) {
            continue; // initial value of v
        }

        Z3_ast v1 = NULL;
        if (q->query->opkind == MEMORY_SLICE_ACCESS) {
            uintptr_t conc_value = get_value_from_slice_array(slices_addrs,
                                        slices_count, addr, s_load_size,
                                        &is_out_of_slice_bounds);
            if (is_out_of_slice_bounds) {
                continue;
            }
            v1 = smt_new_const(conc_value, s_load_size * 8);
        } else {
            v1 = get_input_from_slice_array(addr, s_load_size,
                                        slice_start, slice_end, offset_start,
                                        inputs, &is_out_of_slice_bounds);
            if (is_out_of_slice_bounds) {
                continue;
            }
        }

        fetched_slice_values += 1;
        Z3_ast c  = Z3_mk_eq(smt_solver.ctx, s,
                            smt_new_const(addr, sizeof(uintptr_t) * 8));
        c         = optimize_z3_query(c);
        v         = Z3_mk_ite(smt_solver.ctx, c, v1, v);
        v         = optimize_z3_query(v);

        or_args[k++] = Z3_mk_eq(smt_solver.ctx, s,
                                smt_new_const(addr, sizeof(uintptr_t) * 8));
    }

    Z3_ast addr_or = Z3_mk_or(smt_solver.ctx, fetched_slice_values, or_args);

    Z3_ast e      = Z3_mk_eq(smt_solver.ctx, s_expr, v);
    Z3_ast args[] = {e, Z3_mk_eq(smt_solver.ctx, s, z3_addr), addr_or};
    e             = Z3_mk_and(smt_solver.ctx, 3, args);

    free(or_args);
#if 0
    print_z3_ast(e);
#endif
    // printf("Setting sloads_exprs for %lu\n", scale_sload_index(s_load_id));

    symbols_sizes[scale_sload_index(s_load_id) + 1] = sizeof(uintptr_t) * 8;
    symbols_sizes[scale_sload_index(s_load_id)]     = s_load_size * 8;
    symbols_count += 2;
#if 0
    printf("symbols_sizes[%lu] = %lu %p\n", scale_sload_index(s_load_id), s_load_size * 8, symbols_sizes);
    printf("symbols_sizes[%lu] = %lu %p\n", scale_sload_index(s_load_id) + 1, sizeof(uintptr_t) * 8, symbols_sizes);

    for (size_t i = 0; i < symbols_count; i++) {
        assert(symbols_sizes[i]);
        printf("Index=%lu size=%u\n", i, symbols_sizes[i]);
    }
#endif

    SLoad* s_load_obj = malloc(sizeof(SLoad));
    s_load_obj->index = scale_sload_index(s_load_id);
    s_load_obj->expr  = e;
    sloads_exprs      = g_slist_append(sloads_exprs, (gpointer)s_load_obj);

#if USE_FUZZY_SOLVER
    // printf("Assignment: %lu\n", scale_sload_index(s_load_id) + 1);
    z3fuzz_add_assignment(&smt_solver.fuzzy_ctx,
                          scale_sload_index(s_load_id) + 1, z3_addr);

    // printf("Assignment: %lu\n", scale_sload_index(s_load_id));
    z3fuzz_add_assignment(&smt_solver.fuzzy_ctx, scale_sload_index(s_load_id),
                          v);
#endif

    g_hash_table_add(inputs, (gpointer)scale_sload_index(s_load_id));
    g_hash_table_add(inputs, (gpointer)scale_sload_index(s_load_id) + 1);
    z3_ast_exprs[GET_QUERY_IDX(q)] = e;
    update_and_add_deps_to_solver(inputs, GET_QUERY_IDX(q), NULL, NULL);

    g_hash_table_destroy(conc_addrs);
}

static void smt_expr_query(Query* q, OPKIND opkind)
{
#if 0
    SAYF("\nTranslating %s %lu (0x%lx) to Z3...\n", opkind_to_str(opkind),
         GET_QUERY_IDX(q), (uintptr_t)q->query->op2);
#endif
    GHashTable* inputs = NULL;
    Z3_ast z3_query    = smt_query_to_z3_wrapper(q->query->op1, 0, 0, &inputs);
    // SAYF("DONE: Translating %s to Z3\n", opkind_to_str(opkind));

    if (!inputs) {
        // printf("No inputs in %s query\n", opkind_to_str(opkind));
        return;
    }

#if 0
    print_z3_ast(z3_query);
#endif

    uint8_t        has_real_inputs        = 0;
    uint8_t        inputs_are_concretized = 1;
    GHashTableIter iter;
    gpointer       key, value;
    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {

        // printf("Input: %lu\n", (uint64_t) key);

        if (CONST(key) < testcase.size) {
            has_real_inputs = 1;
        } else if (!concretized_sloads[CONST(key)]) {
            has_real_inputs = 1;
        }

        if (g_hash_table_contains(concretized_bytes, key) != TRUE) {

            inputs_are_concretized = 0;
            // printf("Byte %lu is not in concretized bytes.\n", (size_t) key);

            if (opkind == SYMBOLIC_LOAD || opkind == SYMBOLIC_STORE) {
                // printf("Adding byte %lu to concretized bytes.\n", (size_t)
                // key);
                gboolean res = g_hash_table_add(concretized_bytes, key);
                assert(res == TRUE);
            }
        }
    }

    if (!has_real_inputs) {
        // printf("No real inputs. Skipping it.\n");
        return;
    }
#if 0
    if (inputs_are_concretized) {
        // printf("Address is likely to be already concretized. Skipping
        // it.\n");
        return;
    }
#endif
    uintptr_t solution = (uintptr_t)q->query->op2;

    if (config.address_reasoning && is_interesting_memory(solution)) {

#if 0 // Using SMT Solver:
        int       count    = 0;
        Z3_solver solver   = smt_new_solver();
        add_deps_to_solver(inputs, solver);
        while (count < 256) {
            assert(solution);
            Z3_ast c = Z3_mk_eq(smt_solver.ctx, z3_query,
                                smt_new_const(solution, sizeof(uintptr_t) * 8));
            c        = Z3_mk_not(smt_solver.ctx, c);
            Z3_solver_assert(smt_solver.ctx, solver, c);
            SAYF("Running a %s query...\n", opkind_to_str(opkind));
            int r = smt_query_check_eval_uint64(solver, GET_QUERY_IDX(q), z3_query,
                                                &solution, count + 1);
            if (!r)
                break;
            SAYF("New %s target is %lx\n", opkind_to_str(opkind), solution);
            count += 1;
        }
        smt_del_solver(solver);
#else // Fuzzing:

#if USE_FUZZY_SOLVER && 0
        Z3_ast         deps = get_deps(inputs);
        const uint8_t* proof;
        size_t         proof_size;
        uint64_t min = z3fuzz_minimize(&smt_solver.fuzzy_ctx, deps, z3_query,
                                       &proof, &proof_size);
        if (min != solution) {
            smt_dump_testcase(proof, testcase.size, 1, GET_QUERY_IDX(q), 1);
        }
        uint64_t max = z3fuzz_maximize(&smt_solver.fuzzy_ctx, deps, z3_query,
                                       &proof, &proof_size);
        if (max != solution && max != min) {
            smt_dump_testcase(proof, testcase.size, 1, GET_QUERY_IDX(q), 1);
        }
#else
        GHashTable* solutions = g_hash_table_new(NULL, NULL);
        g_hash_table_add(solutions, (gpointer)solution);
        int r = fuzz_query_eval(inputs, z3_query, solutions, GET_QUERY_IDX(q), 0, 0);
        int n_solutions = g_hash_table_size(solutions);
        printf("Found %d solution for %s expr.\n", n_solutions - 1,
               opkind_to_str(opkind));
        g_hash_table_destroy(solutions);
#endif

#endif
    } else {
        // printf("Address is not interesting. Skipping it.\n");
    }

    if (opkind == SYMBOLIC_LOAD || opkind == SYMBOLIC_STORE) {
        Z3_ast c = Z3_mk_eq(smt_solver.ctx, z3_query,
                            smt_new_const(solution, sizeof(uintptr_t) * 8));
#if 0
        get_inputs_expr(c);
#endif
        z3_ast_exprs[GET_QUERY_IDX(q)] = c;
        update_and_add_deps_to_solver(inputs, GET_QUERY_IDX(q), NULL, NULL);
#if USE_FUZZY_SOLVER
        z3fuzz_notify_constraint(&smt_solver.fuzzy_ctx, c);
#endif
    }
}
static void smt_mem_concr_query(Query* q, OPKIND opkind)
{
#if 0
    SAYF("\nTranslating %s %lu to Z3...\n", opkind_to_str(opkind),
         GET_QUERY_IDX(q));
#endif
    GHashTable* inputs = NULL;
    Z3_ast memory_expr = smt_query_to_z3_wrapper(q->query->op1, 0, 0, &inputs);
    // SAYF("DONE: Translating %s to Z3\n", opkind_to_str(opkind));

    if (!inputs) {
        printf("No inputs in %s query\n", opkind_to_str(opkind));
        ABORT();
    }

    uintptr_t conc_val = CONST(q->query->op2);
    Z3_ast    c        = Z3_mk_eq(smt_solver.ctx, memory_expr,
                        smt_new_const(conc_val, SIZE(memory_expr)));

    z3_ast_exprs[GET_QUERY_IDX(q)] = c;
    update_and_add_deps_to_solver(inputs, GET_QUERY_IDX(q), NULL, NULL);
#if USE_FUZZY_SOLVER
    z3fuzz_notify_constraint(&smt_solver.fuzzy_ctx, c);
#endif
}

static void smt_consistency_expr(Query* q)
{
    Expr*     e              = q->query->op1;
    uintptr_t concrete_value = CONST(q->query->op2);
    uintptr_t pc             = q->address;

    GHashTable* inputs = NULL;
    Z3_ast      z3_e   = smt_query_to_z3_wrapper(e, 0, 0, &inputs);

    for (size_t i = 0; i < testcase.size; i++) {
        eval_data[i] = testcase.data[i];
    }

    uintptr_t solution = conc_query_eval_value(smt_solver.ctx, z3_e, eval_data,
                                               symbols_sizes, symbols_count);

    if (concrete_value == solution) {
        printf("\nConsistency check (id=%lu, pc=%lx): OK\n", GET_QUERY_IDX(q),
               pc);
        printf("CHECK: expected=%lx solution=%lx\n", concrete_value, solution);
    } else {
        printf("\nConsistency check (id=%lu, pc=%lx): FAIL\n", GET_QUERY_IDX(q),
               pc);
        printf("CHECK: expected=%lx solution=%lx\n", concrete_value, solution);
        print_z3_ast(z3_e);
        print_expr(e);
        ABORT();
    }

#if DEBUG_FUZZ_EXPR
    if (inputs) {
        printf("Dumping query for debug fuzz expr\n");
        Z3_solver solver = smt_new_solver();
        add_deps_to_solver(inputs, solver);
        smt_dump_debug_query(solver, z3_e, GET_QUERY_IDX(q));
        smt_del_solver(solver);
    }
#endif
}

static void smt_query(Query* q)
{
#if 0
    print_expr(q->query);
#endif

    switch (q->query->opkind) {
        case SYMBOLIC_PC:
            // printf("\nSymbolic PC\n");
            smt_expr_query(q, q->query->opkind);
            break;
        case SYMBOLIC_JUMP_TABLE_ACCESS:
            // printf("\nSymbolic JUMP access\n");
            smt_expr_query(q, q->query->opkind);
            break;
        case MEMORY_SLICE_ACCESS:
        case MEMORY_INPUT_SLICE_ACCESS:
            // printf("\nSymbolic SLICE access %lu\n", GET_QUERY_IDX(q));
            smt_slice_query(q);
            break;
        case SYMBOLIC_LOAD:
            // printf("\nSymbolic LOAD access\n");
            smt_expr_query(q, q->query->opkind);
            break;
        case SYMBOLIC_STORE:
            // printf("\nSymbolic LOAD access\n");
            smt_expr_query(q, q->query->opkind);
            break;
        case MEMORY_CONCRETIZATION:
            // printf("\nMEMORY CONCRETIZATION\n");
            smt_mem_concr_query(q, q->query->opkind);
            break;
        case CONSISTENCY_CHECK:
            smt_consistency_expr(q);
            break;
        default:
            // printf("\nBranch at 0x%lx\n", q->address);
            smt_branch_query(q);
    }
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

    if (expr_pool_shm_id > 0) {
        // printf("SHM: %lu %lu\n", config.expr_pool_shm_key, expr_pool_shm_id);
        shmctl(expr_pool_shm_id, IPC_RMID, NULL);
    }
    if (query_shm_id > 0) {
        shmctl(query_shm_id, IPC_RMID, NULL);
    }
#if BRANCH_COVERAGE == FUZZOLIC
    if (bitmap_shm_id) {
        shmctl(bitmap_shm_id, IPC_RMID, NULL);
    }
#endif

    // SAYF("Deleted POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id,
    // query_shm_id);
}

void sig_handler(int signo)
{
    printf("[SOLVER] Received SIGINT\n\n");
    save_bitmaps();
    cleanup();
    exit(0);
}

void sig_segfault(int signo)
{
    printf("\n[SOLVER] Received SIGSEGV\n\n");
    save_bitmaps();
    cleanup();
    exit(139); // SIGSEGV
}

void sig_usr1(int signo)
{
    printf("\n[SOLVER] Received SIGUSR1\n\n");
    go_signal = 1;
}

static inline void load_initial_testcase()
{
    printf("Loading testcase: %s\n", config.testcase_path);
    char  data[1024 * 1024] = {0};
    FILE* fp                = fopen(config.testcase_path, "r");
    int   r                 = fread(&data, 1, sizeof(data), fp);
    fclose(fp);
    if (r == sizeof(data)) {
        PFATAL("Testcase is too large\n");
    }
    printf("Loaded %d bytes from testcase: %s\n", r, config.testcase_path);
    assert(r > 0);
    testcase.data = malloc(r);
    testcase.size = r;
    memmove(testcase.data, &data, r);

    for (size_t i = 0; i < testcase.size; i++) {
        symbols_sizes[i] = 8;
    }
    symbols_count = testcase.size;
}

static void run_query_from_file(const char* path)
{
    Z3_ast_vector ast_vector = Z3_parse_smtlib2_file(smt_solver.ctx, path, 0,
                                                     NULL, NULL, 0, NULL, NULL);
    Z3_ast_vector_inc_ref(smt_solver.ctx, ast_vector);
    unsigned num_asts = Z3_ast_vector_size(smt_solver.ctx, ast_vector);

    Z3_solver solver = smt_new_solver();
    for (size_t i = 0; i < num_asts; i++) {
        Z3_solver_assert(smt_solver.ctx, solver,
                         Z3_ast_vector_get(smt_solver.ctx, ast_vector, i));
    }
    smt_query_check(solver, 0, 0);
    smt_del_solver(solver);

    Z3_ast_vector_dec_ref(smt_solver.ctx, ast_vector);
    exit(0);
}

int main(int argc, char* argv[])
{
    parse_opts(argc, argv, &config);

    load_initial_testcase();

    signal(SIGINT, sig_handler);
    signal(SIGTERM, sig_handler);
    signal(SIGSEGV, sig_segfault);
    signal(SIGUSR1, sig_usr1);

    smt_init();

    concretized_bytes = g_hash_table_new(NULL, NULL);

#if 0
    run_query_from_file("/home/ercoppa/Desktop/code/fuzzolic/test_case_31.query");
#endif

#if 0
    printf("Expression size: %lu\n", sizeof(Expr));
    printf("Allocating %lu MB for expression pool\n", (sizeof(Expr) * EXPR_POOL_CAPACITY) / (1024 * 1024));
    printf("Allocating %lu MB for query queue\n", (sizeof(Expr*) * EXPR_QUERY_CAPACITY) / (1024 * 1024));
#endif

    printf("[SOLVER] Creating shared memory #1 (key=%lu)...\n", config.expr_pool_shm_key);

    expr_pool_shm_id = shmget(config.expr_pool_shm_key, // IPC_PRIVATE,
                              sizeof(Expr) * EXPR_POOL_CAPACITY,
                              IPC_CREAT | 0666); /*| IPC_EXCL */
    if (expr_pool_shm_id < 0)
        PFATAL("shmget() failed");

    printf("[SOLVER] Creating shared memory #2 (key=%lu)...\n", config.query_shm_key);

    query_shm_id = shmget(config.query_shm_key, // IPC_PRIVATE,
                          sizeof(Query) * EXPR_QUERY_CAPACITY,
                          IPC_CREAT | 0666); /*| IPC_EXCL */
    if (query_shm_id < 0)
        PFATAL("shmget() failed");

#if BRANCH_COVERAGE == FUZZOLIC
    bitmap_shm_id = shmget(config.bitmap_shm_key, // IPC_PRIVATE,
                           sizeof(uint8_t) * BRANCH_BITMAP_SIZE,
                           IPC_CREAT | 0666); /*| IPC_EXCL */
    if (bitmap_shm_id < 0)
        PFATAL("shmget() failed");
#endif

    // SAYF("POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id,
    // query_shm_id);

    // remove on exit
    atexit(cleanup);

    MEM_BARRIER();

    pool = shmat(expr_pool_shm_id, EXPR_POOL_ADDR, 0);
    if (!pool)
        PFATAL("shmat() failed");

    next_query  = shmat(query_shm_id, NULL, 0);
    query_queue = next_query;
    if (!next_query)
        PFATAL("shmat() failed");

    printf("[SOLVER] Attached to shared memories...\n");

    next_query[0].query = 0;

#if BRANCH_COVERAGE == FUZZOLIC
    branch_bitmap = shmat(bitmap_shm_id, NULL, 0);
    if (!branch_bitmap)
        PFATAL("shmat() failed");
#else
    branch_bitmap = calloc(1, BRANCH_BITMAP_SIZE);
#endif

    load_bitmaps();

    // reset pool and query queue (this may take some time...)
    memset(pool, 0, sizeof(Expr) * EXPR_POOL_CAPACITY);
    memset(next_query, 0, sizeof(Query) * EXPR_QUERY_CAPACITY);

    next_query[0].query = (void*)SHM_READY;

    MEM_BARRIER();

    struct timespec polling_time;
    polling_time.tv_sec  = EXPR_QUEUE_POLLING_TIME_SECS;
    polling_time.tv_nsec = EXPR_QUEUE_POLLING_TIME_NS;

    printf("[SOLVER] Waiting for the tracer...\n");

    // wait tracer to finish its job
    while (1) {
        if (go_signal) {
            break;
        } else if (next_query[0].query != (void*)SHM_DONE) {
            nanosleep(&polling_time, NULL);
        } else {
            // printf("Tracer has finished\n");
            break;
        }
    }
    next_query++;

    MEM_BARRIER();

#if 0
    SAYF("Waiting for queries...\n");
#endif

    while (1) {
        if (next_query[0].query == NULL) {
#if 0
            nanosleep(&polling_time, NULL);
#else
            // tracer may have crashed
            break;
#endif
        } else {
            if (next_query[0].query == FINAL_QUERY) {
                SAYF("\n\nReached final query. Exiting...\n");

                printf("Translation time: %lu usecs\n",
                       smt_solver.translation_time);
                printf("Slice reasoning time: %lu usecs\n",
                       smt_solver.slice_reasoning_time);

                save_bitmaps();
                exit(0);
            }

            if (config.timeout > 0) {
                uint64_t total_solving_time = smt_solver.unsat_time +
                                              smt_solver.sat_time +
                                              smt_solver.unknown_time;
                total_solving_time /= 1000;
                // printf("solving time: %lu timeout: %lu \n",
                // total_solving_time, config.timeout);
                if (total_solving_time > config.timeout) {
                    SAYF("\n\nSolving time exceded budget time. Exiting...\n");

                    printf("Translation time: %lu usecs\n",
                           smt_solver.translation_time);
                    printf("Slice reasoning time: %lu usecs\n",
                       smt_solver.slice_reasoning_time);

                    save_bitmaps();
                    exit(0);
                }
            }

#if 0
            SAYF("Got a query... %p\n", next_query);
#endif
            smt_query(&next_query[0]);
            next_query++;
#if 0
            if (GET_QUERY_IDX(next_query) > 5) {
                printf("Exiting...\n");
                save_bitmaps();
                exit(0);
            }
#endif
        }
    }

    return 0;
}
