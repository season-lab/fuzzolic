#include <signal.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "solver.h"
#include "i386.h"

#define EXPR_QUEUE_POLLING_TIME_SECS 0
#define EXPR_QUEUE_POLLING_TIME_NS   5000
#define SOLVER_TIMEOUT_MS            10000

static int expr_pool_shm_id = -1;
Expr*      pool;

static int    query_shm_id = -1;
static Query* next_query;
static Query* query_queue;

typedef struct SMTSolver {
    Z3_context ctx;
    uint64_t   sat_count;
    uint64_t   sat_time;
    uint64_t   unsat_count;
    uint64_t   unsat_time;
    uint64_t   unknown_count;
    uint64_t   unknown_time;
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

typedef struct {
    uint8_t* data;
    size_t   size;
} Testcase;

static Testcase testcase;

Config config = {0};

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

static void smt_init(void)
{
    Z3_config cfg  = Z3_mk_config();
    smt_solver.ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(smt_solver.ctx, smt_error_handler);
    Z3_del_config(cfg);
}

static inline Z3_solver smt_new_solver()
{
    Z3_solver solver = Z3_mk_solver(smt_solver.ctx);
    Z3_solver_inc_ref(smt_solver.ctx, solver);

    Z3_symbol timeout = Z3_mk_string_symbol(smt_solver.ctx, "timeout");
    Z3_params params  = Z3_mk_params(smt_solver.ctx);
    Z3_params_set_uint(smt_solver.ctx, params, timeout, SOLVER_TIMEOUT_MS);
    Z3_solver_set_params(smt_solver.ctx, solver, params);

    return solver;
}

static inline void smt_del_solver(Z3_solver solver)
{
    Z3_solver_dec_ref(smt_solver.ctx, solver);
}

static inline void smt_destroy(void)
{
    if (smt_solver.ctx) {
        Z3_del_context(smt_solver.ctx);
    }
}

static inline void add_deps_to_solver(GHashTable* inputs, size_t query_idx,
                                      Z3_solver solver)
{
    GHashTableIter iter, iter2;
    gpointer       key, value;
    gboolean       res;

    GHashTable* to_be_deallocated = g_hash_table_new(NULL, NULL);
    Dependency* current           = NULL;

    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
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
            // dealocate later
            g_hash_table_add(to_be_deallocated, dep);
        }
    }

    // add exprs as assertions
    g_hash_table_iter_init(&iter, current->exprs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        size_t query_dep_idx = (size_t)key;
        assert(z3_ast_exprs[query_dep_idx]);
        Z3_solver_assert(smt_solver.ctx, solver, z3_ast_exprs[query_dep_idx]);
        // printf("Adding expr %lu for %lu\n", query_dep_idx, query_idx);
    }

    res = g_hash_table_add(current->exprs, (gpointer)query_idx);
    assert(res == TRUE);

    // update dependency graph for each input in current
    g_hash_table_iter_init(&iter, current->inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        size_t input_idx            = (size_t)key;
        dependency_graph[input_idx] = current;
    }

    // housekeeping
    g_hash_table_iter_init(&iter, to_be_deallocated);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        Dependency* dep = (Dependency*)key;
        g_hash_table_destroy(dep->inputs);
        g_hash_table_destroy(dep->exprs);
        free(dep);
    }
}

Z3_ast smt_new_symbol(uintptr_t id, const char* name, size_t n_bits, Expr* e)
{
    assert(id < MAX_INPUTS_EXPRS);
    if (id < MAX_INPUT_SIZE) {
        if (n_bits != 8) {
            print_expr(e);
        }
        assert(n_bits == 8 && "Multi-byte input not yet supported.");
    }
    Z3_ast s = input_exprs[id];
    if (s == NULL) {
        Z3_sort   bv_sort = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
        Z3_symbol s_name  = Z3_mk_string_symbol(smt_solver.ctx, name);
        s                 = Z3_mk_const(smt_solver.ctx, s_name, bv_sort);
        input_exprs[id]   = s;
        // printf("Generating symbolic for input at offset %lu (%p)\n", id,
        //       input_exprs[id]);
    }
    return s;
}

Z3_ast smt_new_const(uint64_t value, size_t n_bits)
{
    Z3_sort bv_sort = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
    Z3_ast  s       = Z3_mk_unsigned_int64(smt_solver.ctx, value, bv_sort);
    return s;
}

static void smt_dump_solution(Z3_model m, size_t idx)
{
    size_t input_size = testcase.size;

    char testcase_name[128];
    int  n = snprintf(testcase_name, sizeof(testcase_name), "test_case_%lu.dat",
                     idx);
    assert(n > 0 && n < sizeof(testcase_name) && "test case name too long");

#if 0
    SAYF("Dumping solution into %s\n", testcase_name);
#endif

    FILE* fp = fopen(testcase_name, "w");
    for (long i = 0; i < input_size; i++) {
        Z3_ast input_slice   = input_exprs[i];
        int    solution_byte = 0;
        if (input_slice) {
            // SAYF("input slice %ld\n", i);
            Z3_ast  solution;
            Z3_bool successfulEval =
                Z3_model_eval(smt_solver.ctx, m, input_slice,
                              Z3_FALSE, // model_completion
                              &solution);
            assert(successfulEval && "Failed to evaluate model");
            if (Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_NUMERAL_AST) {
                Z3_bool successGet = Z3_get_numeral_int(
                    smt_solver.ctx, solution, &solution_byte);
                if (successGet) // && solution_byte
                    printf("Solution[%ld]: 0x%x\n", i, solution_byte);
            } else {
                assert(Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_APP_AST);
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

static void smt_query_check(Z3_solver solver, size_t idx)
{
#if 1
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
            printf("Query is UNSAT\n");
            smt_solver.unsat_count += 1;
            smt_solver.unsat_time += elapsed_microsecs;
            break;
        case Z3_L_UNDEF:
            printf("Query is UNKNOWN\n");
            smt_solver.unknown_count += 1;
            smt_solver.unknown_time += elapsed_microsecs;
            break;
        case Z3_L_TRUE:
            printf("Query is SAT\n");
            smt_solver.sat_count += 1;
            smt_solver.sat_time += elapsed_microsecs;
            m = Z3_solver_get_model(smt_solver.ctx, solver);
            if (m) {
                Z3_model_inc_ref(smt_solver.ctx, m);
                smt_dump_solution(m, idx);
            }
            break;
    }
    if (m)
        Z3_model_dec_ref(smt_solver.ctx, m);
#endif
}

static void print_z3_original(Z3_ast e)
{
    Z3_set_ast_print_mode(smt_solver.ctx, Z3_PRINT_LOW_LEVEL);
    const char* z3_query_str = Z3_ast_to_string(smt_solver.ctx, e);
    SAYF("\n%s\n", z3_query_str);
}

static void print_z3_ast_internal(Z3_ast e, uint8_t invert_op,
                                  uint8_t parent_is_concat)
{
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
            assert(r == Z3_TRUE);
            printf("%lx#%lu", value, size);
            return;
        }

        case Z3_APP_AST: {

            app          = Z3_to_app(ctx, e);
            decl         = Z3_get_app_decl(ctx, app);
            decl_kind    = Z3_get_decl_kind(ctx, decl);
            num_operands = Z3_get_app_num_args(ctx, app);

            switch (decl_kind) {

                case Z3_OP_UNINTERPRETED: {
                    Z3_symbol   symbol = Z3_get_decl_name(ctx, decl);
                    const char* s      = Z3_get_symbol_string(ctx, symbol);
                    printf("%s", s);
                    return;
                }

                case Z3_OP_TRUE:
                    printf("TRUE");
                    return;
                case Z3_OP_FALSE:
                    printf("FALSE");
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
                case Z3_OP_SIGN_EXT: {
                    assert(invert_op == 0);
                    break;
                }

                case Z3_OP_AND: {
                    s_op = "&&";
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
                    // printf("OTHER");
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

            } else if (decl_kind == Z3_OP_BNOT) {

                printf("%s", s_op);
                print_z3_ast_internal(op1, 0, 0);

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
        printf("\nNumber of operands: %u\n", num_operands);
        print_z3_original(e);
        ABORT();
    }
}

static void print_z3_ast(Z3_ast e)
{
    // print_z3_original(e);
    printf("\n");
    print_z3_ast_internal(e, 0, 0);
    printf("\n\n");
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
        return Z3_mk_ite(smt_solver.ctx, e, smt_new_const(1, width * 8),
                         smt_new_const(0, width * 8));
    } else {
        return e;
    }
}

#define APP(e)    ((Z3_app)e)
#define N_ARGS(e) Z3_get_app_num_args(smt_solver.ctx, APP(e))
#define ARG1(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 0)
#define ARG2(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 1)
#define ARG3(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 2)
#define PARAM1(e)                                                              \
    Z3_get_decl_int_parameter(smt_solver.ctx,                                  \
                              Z3_get_app_decl(smt_solver.ctx, APP(e)), 0);
#define PARAM2(e)                                                              \
    Z3_get_decl_int_parameter(smt_solver.ctx,                                  \
                              Z3_get_app_decl(smt_solver.ctx, APP(e)), 1);
#define OP(e) get_op(APP(e))
#define SIZE(e)                                                                \
    Z3_get_bv_sort_size(smt_solver.ctx, Z3_get_sort(smt_solver.ctx, e))

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
        assert(r == Z3_TRUE);
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
        assert(r == Z3_TRUE);
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
    size_t  a_size = Z3_get_bv_sort_size(smt_solver.ctx, a_sort);
    size_t  b_size = Z3_get_bv_sort_size(smt_solver.ctx, b_sort);
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
    printf("size=%ld a_size=%lu b_size=%lu\n", size, a_size, b_size);
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

        default:
            ABORT();
    }
}

static inline uint8_t get_shifted_bytes(Z3_ast e, Z3_ast* bytes, int n)
{
    if (OP(e) == Z3_OP_BSHL) {
        // printf("Check SHL\n");
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
        Z3_ast  bytes_concat[8] = {0};
        uint8_t r               = get_shifted_bytes(ARG1(e), bytes_concat, 8);
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
                // print_z3_ast_internal(byte, 0);
                // printf("\nbyte_index=%d new_index=%d value=%lu\n",
                // byte_index, new_index, value);

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
            Z3_ast  bytes_1[8] = {0};
            uint8_t r          = get_shifted_bytes(ARG1(e), bytes_1, 8);
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
            Z3_ast  bytes_1[8] = {0};
            uint8_t r          = get_shifted_bytes(ARG2(e), bytes_1, 8);
            if (!r) {
                return 0;
            }
            for (size_t i = 0; i < 8; i++) {
                if (bytes_1[i]) {
                    if (bytes[(SIZE(ARG1(e)) / 8) + i]) {
                        // printf("Check CONCAT KO 7 %lu %p\n", i,
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

    } else if (OP(e) == Z3_OP_BOR) {
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

#define FF_MASK(bits) ((1LU << bits) - 1)

Z3_ast optimize_z3_query(Z3_ast e)
{
#if 0
    printf("\nTransformation on: ");
    print_z3_ast_internal(e, 0, 0);
    printf("\n");
#endif

    Z3_context  ctx  = smt_solver.ctx;
    Z3_ast_kind kind = Z3_get_ast_kind(ctx, e);
    if (kind != Z3_APP_AST) {
        return e;
    }

    Z3_decl_kind decl_kind    = OP(e);
    unsigned     num_operands = N_ARGS(e);

    if (decl_kind == Z3_OP_NOT) {
        Z3_ast op1          = ARG1(e);
        Z3_ast op1_original = op1;
        op1                 = optimize_z3_query(op1);
        if (op1_original != op1) {
            return Z3_mk_not(ctx, op1);
        } else {
            return e;
        }
    }

    uint64_t value;

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
            e = get_make_op(decl_kind)(ctx, ARG1(op2), ARG2(op2));
            return optimize_z3_query(e);
        } else if (is_zero_const(op2) && OP(op1) == Z3_OP_BSUB) {
            e = get_make_op(decl_kind)(ctx, ARG1(op1), ARG2(op1));
            return optimize_z3_query(e);
        }

        // from:
        //  (0x0#N .. X#M) op Y#(N+M)
        // where:
        //  Y is a constant smaller than 0xFF
        //  op is a comparison operator
        //  M == 8
        // to:
        //  X == Y
        if (is_const(op2, &value) && value < 0xFF && OP(op1) == Z3_OP_CONCAT &&
            N_ARGS(op1) == 2 && SIZE(ARG2(op1)) == 8 &&
            is_zero_const(ARG1(op1))) {
            op2 = smt_new_const(value, 8);
            e   = get_make_op(decl_kind)(ctx, ARG2(op1), op2);
            return optimize_z3_query(e);
        }

        // from:
        //  (0x0#N .. X#M) == 0#(N+M)
        // to:
        //  X == 0#size(X)
        if (decl_kind == Z3_OP_EQ && is_zero_const(op2) &&
            OP(op1) == Z3_OP_CONCAT && N_ARGS(op1) == 2 &&
            is_zero_const(ARG1(op1))) {
            op2 = smt_new_const(0, SIZE(ARG2(op1)));
            e   = get_make_op(decl_kind)(ctx, ARG2(op1), op2);
            return optimize_z3_query(e);
        }

        // from:
        //  (0x0#N .. X#M) op C#(N+M)
        // where:
        //  - op is an unsigned comparison op
        //  - C <= MASK_FF(M)
        // to:
        //  X == C#size(X)
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

    } else if (decl_kind == Z3_OP_EXTRACT) {

        Z3_ast op1  = ARG1(e);
        int    high = PARAM1(e);
        int    low  = PARAM2(e);

        uint64_t value2;

        if (low == 0 && SIZE(op1) == high + 1) {
            return op1;
        }

        if (low == high && is_const(op1, &value)) {
            return smt_new_const(value >> low, 1);
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
            return e;
        }

        // from:
        //   (0#M .. X)[high:0]))
        // where:
        //   - size(X) == high + 1
        // to:
        //   X
        if (OP(op1) == Z3_OP_CONCAT && is_zero_const(ARG1(op1))) {

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
        if (OP(op1) == Z3_OP_BSUB && OP(ARG1(op1)) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG1(op1))) && is_const(ARG2(op1), &value) &&
            value < FF_MASK(SIZE(ARG2(ARG1(op1))))) {

            if (SIZE(ARG2(ARG1(op1))) == high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvsub(ctx, ARG2(ARG1(op1)), c);
                return optimize_z3_query(e);
            }
        }
        // symmetric
        if (OP(op1) == Z3_OP_BSUB && OP(ARG2(op1)) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG2(op1))) && is_const(ARG1(op1), &value) &&
            value < FF_MASK(SIZE(ARG2(ARG2(op1))))) {

            if (SIZE(ARG2(ARG2(op1))) == high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvsub(ctx, c, ARG2(ARG2(op1)));
                return optimize_z3_query(e);
            }
        }
        // same but with addition
        if (OP(op1) == Z3_OP_BADD && OP(ARG1(op1)) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG1(op1))) && is_const(ARG2(op1), &value) &&
            value < FF_MASK(SIZE(ARG2(ARG1(op1))))) {

            if (SIZE(ARG2(ARG1(op1))) == high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvadd(ctx, ARG2(ARG1(op1)), c);
                return optimize_z3_query(e);
            }
        }
        // symmetric with addition
        if (OP(op1) == Z3_OP_BADD && OP(ARG2(op1)) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG2(op1))) && is_const(ARG1(op1), &value) &&
            value < FF_MASK(SIZE(ARG2(ARG2(op1))))) {

            if (SIZE(ARG2(ARG2(op1))) == high + 1) {
                Z3_ast c = smt_new_const(value, high + 1);
                e        = Z3_mk_bvadd(ctx, c, ARG2(ARG2(op1)));
                return optimize_z3_query(e);
            }
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
                return e;
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

    } else if (decl_kind == Z3_OP_BOR) {
        assert(num_operands == 2);

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        uint64_t value;
        if (is_zero_const(op1)) {
            return op2;
        }
        if (OP(op1) == Z3_OP_EXTRACT && is_zero_const(ARG1(op1))) {
            return op2;
        }
        if (is_zero_const(op2)) {
            return op1;
        }
        if (OP(op2) == Z3_OP_EXTRACT && is_zero_const(ARG1(op2))) {
            return op1;
        }

        Z3_ast  bytes[8] = {0};
        uint8_t r        = get_shifted_bytes(e, bytes, 8);
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

        // from:
        //   (Y .. ((0#M .. X)[high:0]))
        // where:
        //   - size(X) == high + 1
        // to:
        //   Y .. X
        if (OP(op2) == Z3_OP_EXTRACT && OP(ARG1(op2)) == Z3_OP_CONCAT &&
            is_zero_const(ARG1(ARG1(op2)))) {

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
            is_zero_const(ARG1(op2))) {

            op1 = smt_new_const(0, SIZE(op1) + SIZE(ARG1(op2)));
            e   = Z3_mk_concat(ctx, op1, ARG2(op2));
            return optimize_z3_query(e);
        }

    } else if (decl_kind == Z3_OP_BAND) {

        Z3_ast op1 = ARG1(e);
        Z3_ast op2 = ARG2(e);

        uint64_t value, value2;
        if (is_const(op1, &value) && is_const(op2, &value2)) {
            return smt_new_const(value & value2, SIZE(e));
        }

        if (is_zero_const(op1)) {
            return op2;
        }

        if (is_zero_const(op2)) {
            return op1;
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
            return e;
        }
    } else if (decl_kind == Z3_OP_ITE) {

        if (is_const(ARG1(e), &value)) {
            if (value) {
                return ARG2(e);
            } else {
                return ARG3(e);
            }
        }
    }

    return e;
}

#define VERBOSE 0
Z3_ast smt_query_to_z3(Expr* query, uintptr_t is_const_value, size_t width,
                       GHashTable* inputs)
{
    if (width <= 0)
        width = sizeof(void*);

    if (is_const_value) {
        // printf("IS_CONST: %lx\n", (uintptr_t)query);
        return smt_new_const((uintptr_t)query, 8 * width);
    }

    if (query == NULL)
        return Z3_mk_true(smt_solver.ctx);

    // printf("START opkind: %s\n", opkind_to_str(query->opkind));

    Z3_ast   op1 = NULL;
    Z3_ast   op2 = NULL;
    Z3_ast   r   = NULL;
    unsigned n   = 0;
    switch (query->opkind) {
        case RESERVED:
            ABORT("Invalid opkind (RESERVER). There is a bug somewhere :(");
        case IS_SYMBOLIC:;
            char* input_name = malloc(16);
            if (CONST(query->op1) < MAX_INPUT_SIZE) {
                snprintf(input_name, 16, "input_%lu", (uintptr_t)query->op1);
            } else {
                snprintf(input_name, 16, "s_load_%lu", (uintptr_t)query->op1);
            }
            r = smt_new_symbol((uintptr_t)query->op1, input_name,
                               8 * (uintptr_t)query->op2, query);
            g_hash_table_add(inputs, (void*)query->op1);
            break;
        case IS_CONST:
            r = smt_new_const((uintptr_t)query->op1, 64);
            break;
        //
        case NOT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
#if VERBOSE
            printf("NOT\n");
            smt_print_ast_sort(op1);
#endif
            r = Z3_mk_bvnot(smt_solver.ctx, op1);
            break;
        //
        case NEG:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
#if VERBOSE
            printf("NEG\n");
            smt_print_ast_sort(op1);
#endif
            r = Z3_mk_bvneg(smt_solver.ctx, op1);
            break;
        //
        case ADD:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("DIVU\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvudiv(smt_solver.ctx, op1, op2);
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

            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);

            if (ea && ea->result) {
                assert(Z3_get_sort_kind(smt_solver.ctx,
                                        Z3_get_sort(smt_solver.ctx, op1)) !=
                       Z3_BOOL_SORT);
                printf("EFLAGS: optimized flag extraction\n");
                r = ea->result;
            } else {
                op2 =
                    smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
                assert(query->op3 == 0);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            smt_bv_resize(&op1, &op2, (ssize_t)query->op3);
#if VERBOSE
            printf("SHL\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvshl(smt_solver.ctx, op1, op2);
            break;
        case SHR: // 15
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            assert(query->op3 == 0);
#if VERBOSE
            printf("SHR\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvlshr(smt_solver.ctx, op1, op2);
            break;
        case SAR:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            assert(query->op3 == 0);
#if VERBOSE
            printf("SAR\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvashr(smt_solver.ctx, op1, op2);
            break;
        case ROTL: // 17
            assert(query->op2_is_const && "Second arg of ROL must be concrete");
            op2 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            int pos = (int)(long long)query->op2;
            r       = Z3_mk_rotate_left(smt_solver.ctx, pos, op2);
            break;
        //
        case EQ:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
#if VERBOSE
            printf("EQ\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_eq(smt_solver.ctx, smt_to_bv(op1), smt_to_bv(op2));
            break;
        case NE:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            assert(query->op3 == 0);
            smt_bv_resize(&op1, &op2, 0);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
                                      0, inputs);
            } else {
                op1 =
                    smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            }
            unsigned n = (uintptr_t)query->op2;
#if VERBOSE
            printf("EXTRACT + ZEXT\n");
            smt_print_ast_sort(op1);
#endif
            Z3_sort sort = Z3_get_sort(smt_solver.ctx, op1);
            size_t  size = Z3_get_bv_sort_size(smt_solver.ctx, sort);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
#if VERBOSE
            printf("CONCAT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_concat(smt_solver.ctx, op1, op2);
            break;
        case CONCAT8:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
#if VERBOSE
            printf("CONCAT8\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_concat(smt_solver.ctx, op1, op2);
            break;
        case EXTRACT8:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            unsigned high = ((((uintptr_t)query->op2) + 1) * 8) - 1;
            unsigned low  = ((uintptr_t)query->op2) * 8;
#if VERBOSE
            printf("EXTRACT8\n");
            smt_print_ast_sort(op1);
#endif
            r = Z3_mk_extract(smt_solver.ctx, high, low, op1);
            break;
        case EXTRACT:
            op1  = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            high = (uintptr_t)query->op2;
            low  = (uintptr_t)query->op3;
#if VERBOSE
            printf("EXTRACT\n");
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            op2 = smt_to_bv(op2);
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
        case QZEXTRACT2:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            smt_bv_resize(&op1, &op2, 8);
            if (query->op3 != 0 && CONST(query->op3) != 8) {
                ssize_t s = (ssize_t)query->op3;
                if (s < 0)
                    s = -s;
                op1 = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, op1);
                op2 = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, op2);
                op1 = Z3_mk_sign_ext(smt_solver.ctx, 64 - (s * 8), op1);
                op2 = Z3_mk_sign_ext(smt_solver.ctx, 64 - (s * 8), op2);
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
        case MULU_HIGH:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            smt_bv_resize(&op1, &op2, 8);
            if (query->op3 != 0 && CONST(query->op3) != 8) {
                ssize_t s = (ssize_t)query->op3;
                if (s < 0)
                    s = -s;
                op1 = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, op1);
                op2 = Z3_mk_extract(smt_solver.ctx, s * 8 - 1, 0, op2);
                op1 = Z3_mk_zero_ext(smt_solver.ctx, 64 - (s * 8), op1);
                op2 = Z3_mk_zero_ext(smt_solver.ctx, 64 - (s * 8), op2);
            } else {
                op1 = Z3_mk_zero_ext(smt_solver.ctx, 64, op1);
                op2 = Z3_mk_zero_ext(smt_solver.ctx, 64, op2);
            }
#if VERBOSE
            printf("MUL_HIGH\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvmul(smt_solver.ctx, op1, op2);
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
        case CTZ:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
#if VERBOSE
            printf("CTZ\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            if (op1 != op2) {
                ABORT("Not yet implemented");
            } else {
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
            }
            break;

        // x86 specific
        case RCL:
        case CMP_EQ:
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
                                     width, inputs);
            break;

        default:
            print_expr(query);
            ABORT("Unknown expr opkind: %s", opkind_to_str(query->opkind));
    }

    // printf("%s\n", Z3_ast_to_string(smt_solver.ctx, r));

    // printf("PRE OPTIMIZE\n");
    r = optimize_z3_query(r);
    // printf("POST OPTIMIZE\n");
    // printf("END opkind: %s\n", opkind_to_str(query->opkind));
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

static void smt_branch_query(Query* q)
{
#if 0
    smt_stats(smt_solver.solver);
#endif

    SAYF("Translating query %lu to Z3...\n", GET_QUERY_IDX(q));
    GHashTable* inputs             = g_hash_table_new(NULL, NULL);
    Z3_ast      z3_query           = smt_query_to_z3(q->query, 0, 0, inputs);
    z3_ast_exprs[GET_QUERY_IDX(q)] = z3_query;
    SAYF("DONE: Translating query to Z3\n");

    Z3_ast z3_neg_query = Z3_mk_not(smt_solver.ctx, z3_query); // invert branch
#if 0
    z3_neg_query = Z3_simplify(smt_solver.ctx, z3_neg_query);
#endif

#if 0
    Z3_set_ast_print_mode(smt_solver.ctx, Z3_PRINT_LOW_LEVEL);
    const char* z3_query_str = Z3_ast_to_string(smt_solver.ctx, z3_query);
    SAYF("%s", z3_query_str);
#endif
#if 0
    print_z3_ast(z3_neg_query);
#endif

    uint8_t        has_real_inputs = 0;
    GHashTableIter iter;
    gpointer       key, value;
    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        if ((uintptr_t)key < MAX_INPUT_SIZE) {
            has_real_inputs = 1;
            break;
        }
    }

    if (has_real_inputs && is_interesting_branch(q->address, q->arg0)) {
#if 1
        Z3_solver solver = smt_new_solver();
        add_deps_to_solver(inputs, GET_QUERY_IDX(q), solver);
        Z3_solver_assert(smt_solver.ctx, solver, z3_neg_query);
        SAYF("Running a query...\n");
        smt_query_check(solver, GET_QUERY_IDX(q));
        smt_del_solver(solver);
#endif
    } else {
        printf("Branch is not interesting. Skipping it.\n");
    }

#if 0
    solver = smt_new_solver();
    for (size_t i = 0; i < GET_QUERY_IDX(q); i++) {
        Z3_solver_assert(smt_solver.ctx, solver, z3_ast_exprs[i]);
    }
    Z3_solver_assert(smt_solver.ctx, solver, z3_neg_query);
    smt_dump_solver(solver, GET_QUERY_IDX(q));
    smt_del_solver(solver);
#endif

    g_hash_table_destroy(inputs);
}

static void smt_query(Query* q)
{
#if 0
    print_expr(q->query);
#endif

    switch (q->query->opkind) {
        case SYMBOLIC_PC:
            // ABORT("Not yet implemented"); // ToDo
            break;
        case SYMBOLIC_JUMP_TABLE_ACCESS:
            // ABORT("Not yet implemented"); // ToDo
            break;
        case MEMORY_SLICE_ACCESS:
            // ABORT("Not yet implemented"); // ToDo
            break;
        case SYMBOLIC_LOAD:
            // ABORT("Not yet implemented"); // ToDo
            break;
        case SYMBOLIC_STORE:
            // ABORT("Not yet implemented"); // ToDo
            break;
        default:
            printf("\nBranch at 0x%lx\n", q->address);
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

    if (expr_pool_shm_id > 0)
        shmctl(expr_pool_shm_id, IPC_RMID, NULL);
    if (query_shm_id > 0)
        shmctl(query_shm_id, IPC_RMID, NULL);

    // SAYF("Deleted POOL_SHM_ID=%d QUERY_SHM_ID=%d\n", expr_pool_shm_id,
    // query_shm_id);
}

void sig_handler(int signo)
{
    printf("\n[SOLVER] Received SIGINT\n\n");
    cleanup();
    exit(0);
}

static inline void load_testcase()
{
    printf("Loading testcase: %s\n", config.testcase_path);
    char  data[1024 * 100] = {0};
    FILE* fp               = fopen(config.testcase_path, "r");
    int   r                = fread(&data, 1, sizeof(data), fp);
    fclose(fp);
    if (r == sizeof(data)) {
        PFATAL("Testcase is too large\n");
    }
    printf("Loaded %d bytes from testcase: %s\n", r, config.testcase_path);
    assert(r > 0);
    testcase.data = malloc(r);
    testcase.size = r;
    memmove(testcase.data, &data, r);
}

int main(int argc, char* argv[])
{
    parse_opts(argc, argv, &config);

    load_testcase();
    load_bitmaps();

    signal(SIGINT, sig_handler);
    signal(SIGTERM, sig_handler);

    smt_init();

#if 0
    printf("Expression size: %lu\n", sizeof(Expr));
    printf("Allocating %lu MB for expression pool\n", (sizeof(Expr) * EXPR_POOL_CAPACITY) / (1024 * 1024));
    printf("Allocating %lu MB for query queue\n", (sizeof(Expr*) * EXPR_QUERY_CAPACITY) / (1024 * 1024));
#endif

    expr_pool_shm_id = shmget(EXPR_POOL_SHM_KEY, // IPC_PRIVATE,
                              sizeof(Expr) * EXPR_POOL_CAPACITY,
                              IPC_CREAT | 0666); /*| IPC_EXCL */
    if (expr_pool_shm_id < 0)
        PFATAL("shmget() failed");

    query_shm_id = shmget(QUERY_SHM_KEY, // IPC_PRIVATE,
                          sizeof(Query) * EXPR_QUERY_CAPACITY,
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

    next_query  = shmat(query_shm_id, NULL, 0);
    query_queue = next_query;
    if (!next_query)
        PFATAL("shmat() failed");

    next_query[0].query = 0;

    // reset pool and query queue (this may take some time...)
    memset(pool, 0, sizeof(Expr) * EXPR_POOL_CAPACITY);
    memset(next_query, 0, sizeof(Query) * EXPR_QUERY_CAPACITY);

    next_query[0].query = (void*)SHM_READY;
    next_query++;

    struct timespec polling_time;
    polling_time.tv_sec  = EXPR_QUEUE_POLLING_TIME_SECS;
    polling_time.tv_nsec = EXPR_QUEUE_POLLING_TIME_NS;
#if 0
    SAYF("Waiting for queries...\n");
#endif

    while (1) {
        if (next_query[0].query == NULL) {
            nanosleep(&polling_time, NULL);
        } else {
            if (next_query[0].query == FINAL_QUERY) {
                SAYF("Reached final query. Exiting...\n");
                exit(0);
            }
#if 0
            SAYF("Got a query...\n");
#endif
            smt_query(&next_query[0]);
            next_query++;
#if 0
            if (GET_QUERY_IDX(next_query) > 550) {
                printf("Exiting...\n");
                exit(0);
            }
#endif
        }
    }

    return 0;
}