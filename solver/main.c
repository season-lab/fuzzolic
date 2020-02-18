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

SMTSolver smt_solver;

typedef struct Dependency {
    GHashTable* inputs;
    GHashTable* exprs;
} Dependency;

static Z3_ast      input_exprs[MAX_INPUT_SIZE * 2]      = {NULL};
static Z3_ast      z3_ast_exprs[EXPR_QUERY_CAPACITY]    = {0};
static Dependency* dependency_graph[MAX_INPUT_SIZE * 2] = {0};

static uint8_t*    testcase       = NULL;
static size_t      testcase_size  = 0;
static const char* testcase_fname = NULL;
static char        testcase_delta = 0;

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
#if 0
    FILE* f = fopen(fname, "r");
    fseek(f, 0L, SEEK_END);
    size_t sz = ftell(f);
    fclose(f);
    return sz;
#endif
    assert(testcase_size > 0);
    return testcase_size;
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

static void smt_destroy(void)
{
    assert(smt_solver.ctx);
    Z3_del_context(smt_solver.ctx);
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
        // res = g_hash_table_add(inputs_to_check, input_idx);
        // assert(res == TRUE);

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
    assert(id < MAX_INPUT_SIZE * 2);
    if (id < MAX_INPUT_SIZE) {
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
    size_t input_size = get_input_size(testcase_fname);

    char test_case_name[128];
    int  n = snprintf(test_case_name, sizeof(test_case_name),
                     "test_case_%lu.dat", idx);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    // SAYF("Dumping solution into %s\n", test_case_name);
    FILE* fp = fopen(test_case_name, "w");
    for (long i = 0; i < input_size; i++) {
        Z3_ast input_slice   = input_exprs[i];
        int    solution_byte = 0;
        if (input_slice) {
            // SAYF("input slice %ld\n", i);
            Z3_ast  solution;
            Z3_bool successfulEval = Z3_model_eval(
                smt_solver.ctx, m, input_slice,
                testcase_delta ? Z3_FALSE : Z3_TRUE, // model_completion
                &solution);
            assert(successfulEval && "Failed to evaluate model");
            if (Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_NUMERAL_AST) {
                Z3_bool successGet = Z3_get_numeral_int(
                    smt_solver.ctx, solution, &solution_byte);
                if (successGet) // && solution_byte
                    printf("Solution[%ld]: 0x%x\n", i, solution_byte);
            } else {
                assert(Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_APP_AST);
                solution_byte = i < testcase_size ? testcase[i] : 0;
            }
        } else {
            // printf("Input slice is not used by the formula\n");
            solution_byte = i < testcase_size ? testcase[i] : 0;
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
        *a = Z3_mk_concat(smt_solver.ctx, smt_new_const(0, size - a_size), *a);
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
        *b = Z3_mk_concat(smt_solver.ctx, smt_new_const(0, size - b_size), *b);
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

#define VERBOSE 0
Z3_ast smt_query_to_z3(Expr* query, uintptr_t is_const, size_t width,
                       GHashTable* inputs)
{
    if (width <= 0)
        width = sizeof(void*);

    if (is_const) {
        // printf("IS_CONST: %lx\n", (uintptr_t)query);
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
            r = Z3_mk_bvadd(smt_solver.ctx, op1, op2);
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
            assert(query->op3 == 0);
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
#if VERBOSE
            printf("LT\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvslt(smt_solver.ctx, op1, op2);
            break;
        case GE:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            assert(query->op3 == 0);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            n   = (uintptr_t)query->op2;
            op1 = Z3_mk_extract(smt_solver.ctx, n - 1, 0, op1);
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
            r = Z3_mk_extract(smt_solver.ctx, high, low, op1);
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
            r  = Z3_mk_bvor(smt_solver.ctx, r0, r1);
            break;
        //
        case QZEXTRACT2:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0, inputs);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 0, inputs);
            smt_bv_resize(&op1, &op2, 8);
            dpos = (uintptr_t)query->op3;
#if 0
            printf("QZEXTRACT2\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r  = Z3_mk_concat(smt_solver.ctx, op2, op1);
            r  = Z3_mk_extract(smt_solver.ctx, dpos + 64 - 1, dpos, r);
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
            assert(query->op3 == 0);
            op1 = Z3_mk_concat(smt_solver.ctx, smt_new_const(0, 64), op1);
            op2 = Z3_mk_concat(smt_solver.ctx, smt_new_const(0, 64), op2);
#if VERBOSE
            printf("MULU_HIGH\n");
            smt_print_ast_sort(op1);
            smt_print_ast_sort(op2);
#endif
            r = Z3_mk_bvmul(smt_solver.ctx, op1, op2);
            r = Z3_mk_extract(smt_solver.ctx, 127, 64, r);
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
            r = smt_query_i386_to_z3(smt_solver.ctx, query, is_const, width,
                                     inputs);
            break;

        default:
            ABORT("Unknown expr opkind: %s", opkind_to_str(query->opkind));
    }

    // printf("%s\n", Z3_ast_to_string(smt_solver.ctx, r));
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

#if 1
    Z3_set_ast_print_mode(smt_solver.ctx, Z3_PRINT_LOW_LEVEL);
    const char* z3_query_str = Z3_ast_to_string(smt_solver.ctx, z3_query);
    SAYF("%s", z3_query_str);
#endif

    uint8_t has_real_inputs = 0;
    GHashTableIter iter;
    gpointer       key, value;
    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        if ((uintptr_t) key < MAX_INPUT_SIZE) {
            has_real_inputs = 1;
            break;
        }
    }

    if (has_real_inputs) {
        Z3_solver solver = smt_new_solver();
        add_deps_to_solver(inputs, GET_QUERY_IDX(q), solver);
        Z3_solver_assert(smt_solver.ctx, solver, z3_neg_query);
        SAYF("Running a query...\n");
        smt_query_check(solver, GET_QUERY_IDX(q));
        smt_del_solver(solver);
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
            ABORT("Not yet implemented"); // ToDo
            break;
        case SYMBOLIC_JUMP_TABLE_ACCESS:
            ABORT("Not yet implemented"); // ToDo
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
    printf("\nReceived SIGINT\n\n");
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
            printf("Query is UNKNOWN\n");
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

static inline void load_testcase()
{
    printf("Loading testcase: %s\n", testcase_fname);
    char  data[1024 * 100] = {0};
    FILE* fp               = fopen(testcase_fname, "r");
    int   r                = fread(&data, 1, sizeof(data), fp);
    fclose(fp);
    if (r == sizeof(data))
        PFATAL("Testcase is too large\n");
    printf("Loaded %d bytes from testcase: %s\n", r, testcase_fname);
    assert(r > 0);
    testcase      = malloc(r);
    testcase_size = r;
    memmove(testcase, &data, r);
}

int main(int argc, char* argv[])
{
    smt_init();

    if (argc < 3) {
        printf("%s <testcase> <testcase_dir> [-d]\n", argv[0]);
        printf("%s -q <testcase.query>\n", argv[0]);
        exit(1);
    }

    if (argc == 3 && strcmp("-q", argv[1]) == 0) {
        smt_load_solver(argv[2]);
        return 0;
    } else {
        testcase_fname = argv[1];
        load_testcase();
        if (argc == 4 && strcmp("-d", argv[3]) == 0)
            testcase_delta = 1;
    }

    signal(SIGINT, sig_handler);

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
            if (GET_QUERY_IDX(next_query) > 2000) {
                printf("Exiting...\n");
                exit(0);
            }
#endif
        }
    }

    return 0;
}