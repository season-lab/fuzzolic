#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <time.h>
#include <unistd.h>

#include <z3.h>
#define Z3_VERSION 487

#define USE_COLOR
#include "debug.h"

#define EXPR_QUEUE_POLLING_TIME_SECS 0
#define EXPR_QUEUE_POLLING_TIME_NS 5000

#include "index-queue.h"
#include "../tracer/tcg/symbolic/symbolic-struct.h"

static unsigned char* testcase_bytes   = 0;
static unsigned char* tmp_testcase     = 0;
static unsigned long  testcase_len     = 0;
static int            expr_pool_shm_id = -1;
Expr*                 pool;

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

#if Z3_VERSION <= 441
static void smt_error_handler(Z3_context c)
#else
static void smt_error_handler(Z3_context c, Z3_error_code e)
#endif
{
#if Z3_VERSION <= 441
    printf("Error code: %s\n", Z3_get_error_msg(smt_solver.ctx));
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

static void init_testcase(char* filename)
{
    FILE*         fp = fopen(filename, "r");
    int           res, i = 0;
    unsigned char c;

    if (fp == NULL)
        PFATAL("fopen() failed");

    fseek(fp, 0L, SEEK_END);
    testcase_len = ftell(fp);
    fseek(fp, 0L, SEEK_SET);

    testcase_bytes =
        (unsigned char*)malloc(sizeof(unsigned char) * testcase_len);
    tmp_testcase = (unsigned char*)malloc(sizeof(unsigned char) * testcase_len);

    while (1) {
        res = fread(&c, sizeof(char), 1, fp);
        if (res != 1)
            break;
        testcase_bytes[i] = c;
        tmp_testcase[i++] = c;
    }
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
    int n = snprintf(test_case_name, sizeof(test_case_name), "test_case_%u.dat",
                     file_next_id++);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    // SAYF("Dumping solution into %s\n", test_case_name);
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

static void smt_dump_solution_from_buffer(unsigned char* model)
{
    char test_case_name[128];
    int n = snprintf(test_case_name, sizeof(test_case_name), "test_case_%u.dat",
                     file_next_id++);
    assert(n > 0 && n < sizeof(test_case_name) && "test case name too long");
    // SAYF("Dumping solution into %s\n", test_case_name);
    FILE* fp = fopen(test_case_name, "w");
    for (unsigned long i = 0; i < testcase_len; i++) {
        fwrite(&model[i], sizeof(unsigned char), 1, fp);
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
    // printf("Sort: %s\n", Z3_sort_to_string(smt_solver.ctx, sort));
}

static inline void reset_tmp_testcase()
{
    memcpy(tmp_testcase, testcase_bytes, testcase_len);
}

static inline unsigned char extract_from_long(unsigned long value,
                                              unsigned int  i)
{
    return (value >> i * 8) & 0xff;
}

static inline int visit_concat_chain(Expr* e, unsigned int group)
// if 1 -> error
{
    int r, tmp1, tmp2;
    switch (e->opkind) {
        case RESERVED:
            ABORT("Invalid opkind (RESERVER). There is a bug somewhere :(");
        case IS_SYMBOLIC:
            ABORT("Shouldn't be here (IS_SYMBOLIC). Maybe symbol without "
                  "extract?");
        case CONCAT8:
            tmp1 = visit_concat_chain(e->op1, group);
            tmp2 = visit_concat_chain(e->op2, group);
            r    = tmp1 | tmp2;
            break;
        case EXTRACT8:
            if (e->op1->opkind == IS_SYMBOLIC) {
                r = 0;
                ADD_INDEX((unsigned long)e->op2, group);
            } else
                r = 1;
            break;
        default:
            r = 1;
    }
    return r;
}

static int get_indexes_and_values_to_fuzz(Expr* e, unsigned long is_const,
                                          char* is_bool)
// if 1 -> no index to fuzz
{
    int  r, tmp1, tmp2;
    char tmp1_b = 0, tmp2_b = 0;

    if (is_const) {
        *is_bool = 0;
#ifdef ADD_VALUE_ALWAYS
        r = HAS_VALUE;
        ADD_VALUE((unsigned long)e);
        return r;
#else
        return 0;
#endif
    }

    switch (e->opkind) {
        case RESERVED:
            ABORT("Invalid opkind (RESERVER). There is a bug somewhere :(");
        case IS_SYMBOLIC:
            ABORT("Shouldn't be here (IS_SYMBOLIC). Maybe symbol without "
                  "extract?");
        case IS_CONST:
            ABORT("Shouldn't be here (IS_CONST).");
        case ZEXT:
        case NEG:
            *is_bool = 0;
            r        = get_indexes_and_values_to_fuzz(
                e->op1, (unsigned long)e->op1_is_const, &tmp1_b);
            assert(tmp1_b == 0);
            break;
        case ADD:
        case SUB:
            tmp1     = get_indexes_and_values_to_fuzz(e->op1, e->op1_is_const,
                                                  &tmp1_b);
            tmp2     = get_indexes_and_values_to_fuzz(e->op2, e->op2_is_const,
                                                  &tmp2_b);
            *is_bool = 0;
            r        = tmp1 | tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        case AND:
            tmp1 = get_indexes_and_values_to_fuzz(e->op1, e->op1_is_const,
                                                  &tmp1_b);
            tmp2 = get_indexes_and_values_to_fuzz(e->op2, e->op2_is_const,
                                                  &tmp2_b);
            if (tmp1_b && tmp2_b) {
                *is_bool = 1;
            } else {
                assert(tmp1_b == 0 && tmp2_b == 0);
                *is_bool = 0;
            }
            r = tmp1 | tmp2;
            break;
        case EQ:
        case NE:
        case LTU:
        case LEU:
        case GEU:
        case GTU:
            r = 0;
#ifndef ADD_VALUE_ALWAYS
            if (e->op1_is_const && !e->op2_is_const) {
                ADD_VALUE((unsigned long)e->op1);
                r = HAS_VALUE;
            } else if (e->op2_is_const && !e->op1_is_const) {
                ADD_VALUE((unsigned long)e->op2);
                r = HAS_VALUE;
            }
#endif
            *is_bool = 1;
            tmp1     = get_indexes_and_values_to_fuzz(e->op1, e->op1_is_const,
                                                  &tmp1_b);
            tmp2     = get_indexes_and_values_to_fuzz(e->op2, e->op2_is_const,
                                                  &tmp2_b);
            assert(tmp1_b == 0 && tmp2_b == 0);
            r = r | tmp1 | tmp2;
            break;
        case CONCAT8:
            r                  = 0;
            unsigned int group = index_queue.size;
            if (group < index_queue.size_max) {
                index_queue.index_groups[group].n = 0;
                if (visit_concat_chain(e, group) == 0) {
                    index_queue.size += 1;
                    r = HAS_INDEX;
                }
            }
            if (r == 0) { // visit_concat_chain failed or no more groups
                tmp1 = get_indexes_and_values_to_fuzz(e->op1, e->op1_is_const,
                                                      &tmp1_b);
                tmp2 = get_indexes_and_values_to_fuzz(e->op2, e->op2_is_const,
                                                      &tmp2_b);
                r    = tmp1 | tmp2;
            }
            *is_bool = 0;
            break;
        case EXTRACT8:
            if (e->op1->opkind == IS_SYMBOLIC) {
                r                  = 0;
                unsigned int group = index_queue.size;
                if (group < index_queue.size_max) {
                    index_queue.size++;
                    index_queue.index_groups[group].n = 1;
                    index_queue.index_groups[group].indexes[0] =
                        (unsigned long)e->op2;
                    r = HAS_INDEX;
                }
            } else {
                tmp1 = get_indexes_and_values_to_fuzz(e->op1, e->op1_is_const,
                                                      &tmp1_b);
                r    = tmp1;
                assert(tmp1_b == 0);
            }
            *is_bool = 0;
            break;
        default:
            ABORT("Unknown expr opkind: %u", e->opkind);
    }
    return r;
}

static unsigned long evaluate_expression(Expr* e, unsigned char* model,
                                         unsigned long is_const, char* is_bool)
{
    unsigned long r = 0, tmp1 = 0, tmp2 = 0;
    char          tmp1_b = 0, tmp2_b = 0;

    if (is_const)
        return (unsigned long)e;

    switch (e->opkind) {
        case RESERVED:
            ABORT("Invalid opkind (RESERVER). There is a bug somewhere :(");
        case IS_SYMBOLIC:
            ABORT("Shouldn't be here (IS_SYMBOLIC). Maybe symbol without "
                  "extract?");
        case IS_CONST:
            *is_bool = 0;
            r        = (unsigned long)e->op1;
            break;
        //
        case NEG:
            *is_bool = 0;
            r = ~evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            assert(tmp1_b == 0);
            break;
        //
        case ADD:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 0;
            r        = tmp1 + tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        case SUB:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 0;
            r        = tmp1 - tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        case AND:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);

            if (tmp1_b && tmp2_b) {
                r        = tmp1 && tmp2;
                *is_bool = 1;
            } else {
                assert(tmp1_b == 0 && tmp2_b == 0);
                r        = tmp1 & tmp2;
                *is_bool = 0;
            }
            break;
        //
        case EQ:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 1;
            r        = tmp1 == tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        case NE:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 1;
            r        = tmp1 != tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        //
        case LTU:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 1;
            r        = tmp1 < tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        case LEU:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 1;
            r        = tmp1 <= tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        case GEU:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 1;
            r        = tmp1 >= tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        case GTU:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 1;
            r        = tmp1 > tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;
        //
        case ZEXT:
            *is_bool = 0;
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            unsigned long to_extract = 64 - (unsigned long)e->op2;
            r                        = tmp1 & ((2l << (to_extract - 1)) - 1);
            assert(tmp1_b == 0);
            break;
        //
        case CONCAT8:
            tmp1 = evaluate_expression(e->op1, model, e->op1_is_const, &tmp1_b);
            tmp2 = evaluate_expression(e->op2, model, e->op2_is_const, &tmp2_b);
            *is_bool = 0;
            r        = (tmp1 << 8) | tmp2;
            assert(tmp1_b == 0 && tmp2_b == 0);
            break;

        case EXTRACT8:
            if (e->op1->opkind == IS_SYMBOLIC) {
                *is_bool = 0;
                r        = model[(unsigned long)e->op2];
            } else {
                tmp1     = evaluate_expression(e->op1, model, e->op1_is_const,
                                           &tmp1_b);
                *is_bool = 0;
                unsigned long high = ((((unsigned long)e->op2) + 1) * 8) - 1;
                unsigned long low  = (((unsigned long)e->op2) * 8);
                r                  = (tmp1 >> low) & ((2 << (high - low)) - 1);
                assert(tmp1_b == 0);
            }
            break;
        default:
            ABORT("Unknown expr opkind: %u", e->opkind);
    }
    return r;
}

static int fuzz_expression(Expr* e)
{
    // if 1 -> branch flipped
    assert(index_queue.size > 0);

    char          is_bool;
    unsigned long res;
    unsigned int  i, j, k;
    index_group_t group;
    unsigned long value;
    for (i = 0; i < value_queue.size; ++i) {
        value = value_queue.values[i];
        for (j = 0; j < index_queue.size; ++j) {
            group = index_queue.index_groups[j];
            SAYF("size of group: %u\n", group.n);
            reset_tmp_testcase();
            for (k = 0; k < group.n; ++k) {
                tmp_testcase[group.n - group.indexes[k] - 1] = // little endian
                    extract_from_long(value, k);
                SAYF("inj byte: 0x%x\n",
                     tmp_testcase[group.n - group.indexes[k] - 1]);
            }
            res = evaluate_expression(e, tmp_testcase, 0, &is_bool);
            assert(is_bool);
            if (res == 1) {
                SAYF("Branch flipped. group: %d. value: 0x%lx\n", j, value);
                return 1;
            }
        }
    }
    return 0;
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
    print_expr(query);

    char is_bool;
    SAYF("Query evaluated in testcase: %lu\n",
         evaluate_expression(query, testcase_bytes, 0, &is_bool));
    SAYF("Query bool? %d\n", is_bool);
    CLEAR_INDEX_VALUE_QUEUE();
    int res = get_indexes_and_values_to_fuzz(query, 0, &is_bool);
    if (res == HAS_INDEX_AND_VALUE) {
        SAYF("Input fuzz is possible!\n");
        print_index_and_value_queue();
        if (fuzz_expression(query)) {
            SAYF("Branch flipped without solver!\n");
            smt_dump_solution_from_buffer(tmp_testcase);
            return;
        }
    }
    SAYF("Slow path...\n");
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
    free(testcase_bytes);
    free(tmp_testcase);
    testcase_bytes = 0;
    tmp_testcase   = 0;

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
    if (argc < 2)
        PFATAL("No testcase filename");

    init_testcase(argv[1]);
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