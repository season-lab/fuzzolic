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

#define FOUND_SUB_AND 1
#define FOUND_COMPARISON 2

// #define DEBUG_CHECK_LIGHT

#define USE_COLOR
#include "debug.h"

#define EXPR_QUEUE_POLLING_TIME_SECS 0
#define EXPR_QUEUE_POLLING_TIME_NS 5000

#include "index-queue.h"
#include "testcase-list.h"
#include "../tracer/tcg/symbolic/symbolic-struct.h"

static int expr_pool_shm_id = -1;
Expr*      pool;

static int    query_shm_id = -1;
static Expr** next_query;

typedef struct evaluate_t {
    Z3_model model;
    int      value;
} evaluate_t;

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

static inline unsigned char extract_from_long(unsigned long value,
                                              unsigned int  i)
{
    return (value >> i * 8) & 0xff;
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

static Expr*     cached_input_expr   = NULL;
static Z3_ast    cached_input        = NULL;
static Z3_symbol cached_input_symbol = NULL;
static Z3_ast    smt_new_symbol(const char* name, size_t n_bits, Expr* e)
{
    // ToDo: support more than one input
    if (cached_input) {
        assert(e->op1 == cached_input_expr->op1 &&
               e->op2 == cached_input_expr->op2);
        return cached_input;
    }

    Z3_sort   bv_sort   = Z3_mk_bv_sort(smt_solver.ctx, n_bits);
    Z3_symbol s_name    = Z3_mk_string_symbol(smt_solver.ctx, name);
    Z3_ast    s         = Z3_mk_const(smt_solver.ctx, s_name, bv_sort);
    cached_input        = s;
    cached_input_symbol = s_name;
    cached_input_expr   = e;
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
        solution = Z3_simplify(smt_solver.ctx,
                               solution); // otherwise, concrete expression...
                                          // idk, probably evaluate problem
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

static inline Z3_ast ast_patch_byte(Z3_ast v, unsigned char b,
                                    unsigned long index, unsigned long size)
{
    // todo. find a way to modify the ast

    assert(index < size && "Index bigger than size");

    Z3_ast tmp1, tmp2, res;
    Z3_ast b_z3 = smt_new_const((unsigned long)b, 8);
    if (index == 0 && size == 1) {
        res = b_z3;
    } else if (index == size - 1) {
        // last one
        tmp1 = Z3_mk_extract(smt_solver.ctx, (size - 1) * 8 - 1, 0, v);
        tmp1 = Z3_mk_concat(smt_solver.ctx, b_z3, tmp1);
        res  = tmp1;
    } else if (index == 0) {
        // first one
        tmp1 = Z3_mk_extract(smt_solver.ctx, size * 8 - 1, 8, v);
        tmp1 = Z3_mk_concat(smt_solver.ctx, tmp1, b_z3);
        res  = tmp1;
    } else {
        tmp1 = Z3_mk_extract(smt_solver.ctx, size * 8 - 1, (index + 1) * 8, v);
        tmp2 = Z3_mk_extract(smt_solver.ctx, index * 8 - 1, 0, v);
        tmp1 = Z3_mk_concat(smt_solver.ctx, tmp1, b_z3);
        tmp1 = Z3_mk_concat(smt_solver.ctx, tmp1, tmp2);
        res  = tmp1;
    }
    return res;
}

static int ast_find_early_constants(Z3_ast v, unsigned long* sub_add,
                                    unsigned long* comparison)
{
    // look for constants in early SUB/AND and in early EQ/GE/GT/LE/LT
    // 1 -> found sub_add
    // 2 -> found comparison
    // 3 -> found both
    int res = 0;
    switch (Z3_get_ast_kind(smt_solver.ctx, v)) {
        case Z3_APP_AST: {
            Z3_bool      successGet;
            Z3_ast       child1, child2;
            Z3_app       app       = Z3_to_app(smt_solver.ctx, v);
            Z3_func_decl decl      = Z3_get_app_decl(smt_solver.ctx, app);
            Z3_decl_kind decl_kind = Z3_get_decl_kind(smt_solver.ctx, decl);

            switch (decl_kind) {
                case Z3_OP_EXTRACT:
                case Z3_OP_NOT: {
                    // unary forward
                    child1 = Z3_get_app_arg(smt_solver.ctx, app, 0);
                    res = ast_find_early_constants(child1, sub_add, comparison);
                    break;
                }
                case Z3_OP_EQ:
                case Z3_OP_GE:
                case Z3_OP_GT:
                case Z3_OP_LE:
                case Z3_OP_LT: {
                    // binary forward
                    child1 = Z3_get_app_arg(smt_solver.ctx, app, 0);
                    child2 = Z3_get_app_arg(smt_solver.ctx, app, 1);

                    if (Z3_get_ast_kind(smt_solver.ctx, child1) ==
                        Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(smt_solver.ctx,
                                                           child1, comparison);
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        res = FOUND_COMPARISON;
                    } else if (Z3_get_ast_kind(smt_solver.ctx, child2) ==
                               Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(smt_solver.ctx,
                                                           child2, comparison);
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        res = FOUND_COMPARISON;
                    }

                    res |=
                        ast_find_early_constants(child1, sub_add, comparison);
                    res |=
                        ast_find_early_constants(child2, sub_add, comparison);
                    break;
                }
                case Z3_OP_CONCAT: {
                    child1 = Z3_get_app_arg(smt_solver.ctx, app, 0);
                    child2 = Z3_get_app_arg(smt_solver.ctx, app, 1);
                    res |=
                        ast_find_early_constants(child1, sub_add, comparison);
                    res |=
                        ast_find_early_constants(child2, sub_add, comparison);
                    break;
                }
                case Z3_OP_BSUB:
                case Z3_OP_BAND: {
                    // look for constant
                    child1 = Z3_get_app_arg(smt_solver.ctx, app, 0);
                    child2 = Z3_get_app_arg(smt_solver.ctx, app, 1);

                    if (Z3_get_ast_kind(smt_solver.ctx, child1) ==
                        Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(smt_solver.ctx,
                                                           child1, sub_add);
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        res = FOUND_SUB_AND;
                    } else if (Z3_get_ast_kind(smt_solver.ctx, child2) ==
                               Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(smt_solver.ctx,
                                                           child2, sub_add);
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        res = FOUND_SUB_AND;
                    }
                    break;
                }
                default: {
                    break;
                }
            }
            break;
        }
        default: {
            break;
        }
    }
    return res;
}

static int ast_visit_concat_chain(Z3_ast v, unsigned int group)
{
    // group together inputs that belongs to a "concat chain"
    // e.g. (concat (concat (INPUT[7:0], INPUT[15:8])), INPUT[23:16])
    // 1 -> error
    int res;
    switch (Z3_get_ast_kind(smt_solver.ctx, v)) {
        case Z3_APP_AST: {
            Z3_app       app        = Z3_to_app(smt_solver.ctx, v);
            unsigned     num_fields = Z3_get_app_num_args(smt_solver.ctx, app);
            Z3_func_decl decl       = Z3_get_app_decl(smt_solver.ctx, app);
            unsigned     num_params =
                Z3_get_decl_num_parameters(smt_solver.ctx, decl);
            Z3_decl_kind decl_kind = Z3_get_decl_kind(smt_solver.ctx, decl);

            switch (decl_kind) {
                case Z3_OP_CONCAT: {
                    assert(num_fields == 2);

                    Z3_ast sx_child = Z3_get_app_arg(smt_solver.ctx, app, 0);
                    Z3_ast dx_child = Z3_get_app_arg(smt_solver.ctx, app, 1);
                    res             = ast_visit_concat_chain(sx_child, group);
                    res |= ast_visit_concat_chain(dx_child, group);
                    break;
                }
                case Z3_OP_EXTRACT: {
                    assert(num_fields == 1);
                    assert(num_params == 2);

                    Z3_ast       bv = Z3_get_app_arg(smt_solver.ctx, app, 0);
                    Z3_app       bv_app = Z3_to_app(smt_solver.ctx, bv);
                    Z3_func_decl bv_decl =
                        Z3_get_app_decl(smt_solver.ctx, bv_app);
                    Z3_decl_kind bv_decl_kind =
                        Z3_get_decl_kind(smt_solver.ctx, bv_decl);

                    if (bv_decl_kind == Z3_OP_UNINTERPRETED) {
                        // it's a symbol!
                        unsigned int hig =
                            Z3_get_decl_int_parameter(smt_solver.ctx, decl, 0);
                        unsigned int low =
                            Z3_get_decl_int_parameter(smt_solver.ctx, decl, 1);
                        // SAYF("Extract INPUT[%u:%u]\n", hig, low);

                        assert(hig - low + 1 == 8 &&
                               "I'm assuming 1-byte extract from input\n");

                        ADD_INDEX(low / 8, group);
                        res = 0;
                    } else {
                        res = 1;
                    }
                    break;
                }
            }
            break;
        }
        default: {
            res = 1;
            break;
        }
    }
    return res;
}

static void ast_find_involved_inputs(Z3_ast v)
{
    // find "groups" of inputs involved in v and store them in index_queue
    switch (Z3_get_ast_kind(smt_solver.ctx, v)) {
        case Z3_NUMERAL_AST: {
            unsigned long value = -1;
            Z3_bool       successGet =
                Z3_get_numeral_uint64(smt_solver.ctx, v, &value);
            assert(successGet == Z3_TRUE && "failed to get constant");
            ADD_VALUE(value);
            break;
        }
        case Z3_APP_AST: {
            unsigned     i;
            Z3_app       app        = Z3_to_app(smt_solver.ctx, v);
            unsigned     num_fields = Z3_get_app_num_args(smt_solver.ctx, app);
            Z3_func_decl decl       = Z3_get_app_decl(smt_solver.ctx, app);
            unsigned     num_params =
                Z3_get_decl_num_parameters(smt_solver.ctx, decl);
            Z3_decl_kind decl_kind = Z3_get_decl_kind(smt_solver.ctx, decl);

            switch (decl_kind) {
                case Z3_OP_CONCAT: {
                    unsigned int group = index_queue.size;
                    assert(group < index_queue.size_max &&
                           "index_queue is full");
                    index_queue.index_groups[group].n = 0;
                    if (ast_visit_concat_chain(v, group) == 1) {
                        // no concat chain
                        for (i = 0; i < num_fields; i++) {
                            ast_find_involved_inputs(
                                Z3_get_app_arg(smt_solver.ctx, app, i));
                        }
                    } else {
                        // concat chain. commit
                        index_queue.size += 1;
                    }
                    break;
                }
                case Z3_OP_EXTRACT: {
                    assert(num_fields == 1);
                    assert(num_params == 2);
                    Z3_ast       bv = Z3_get_app_arg(smt_solver.ctx, app, 0);
                    Z3_app       bv_app = Z3_to_app(smt_solver.ctx, bv);
                    Z3_func_decl bv_decl =
                        Z3_get_app_decl(smt_solver.ctx, bv_app);
                    Z3_decl_kind bv_decl_kind =
                        Z3_get_decl_kind(smt_solver.ctx, bv_decl);

                    unsigned int group = index_queue.size;
                    assert(group < index_queue.size_max &&
                           "index_queue is full");
                    index_queue.index_groups[group].n = 0;
                    if (bv_decl_kind == Z3_OP_UNINTERPRETED) {
                        // it's a symbol!
                        unsigned int hig =
                            Z3_get_decl_int_parameter(smt_solver.ctx, decl, 0);
                        unsigned int low =
                            Z3_get_decl_int_parameter(smt_solver.ctx, decl, 1);
                        // SAYF("Extract INPUT[%u:%u]\n", hig, low);

                        assert(hig - low + 1 == 8 &&
                               "I'm assuming 1-byte extract from input\n");

                        // add index to queue
                        ADD_INDEX(low / 8, group);
                        // commit (single byte)
                        index_queue.size += 1;
                    } else {
                        // not a symbol. Recursive call
                        ast_find_involved_inputs(bv);
                    }
                    break;
                }
                default: {
                    if (num_fields > 0) {
                        for (i = 0; i < num_fields; i++) {
                            ast_find_involved_inputs(
                                Z3_get_app_arg(smt_solver.ctx, app, i));
                        }
                    }
                    break;
                }
            }
            break;
        }
        case Z3_QUANTIFIER_AST: {
            ABORT("ast_find_involved_inputs() found quantifier\n");
        }
        default:
            ABORT("ast_find_involved_inputs() unknown ast kind\n");
    }
}

static int smt_query_evaluate(Z3_symbol input, Z3_ast input_val, Z3_ast query,
                              evaluate_t* res)
{
    // evaluate query using [input <- input_val] as interpretation

    // build a model and assign an interpretation for the input symbol
    Z3_model     z3_m = Z3_mk_model(smt_solver.ctx);
    Z3_sort      sort = Z3_get_sort(smt_solver.ctx, input_val);
    Z3_func_decl decl = Z3_mk_func_decl(smt_solver.ctx, input, 0, NULL, sort);
    Z3_add_const_interp(smt_solver.ctx, z3_m, decl, input_val);

    // SAYF("query: %s\n", Z3_ast_to_string(smt_solver.ctx, query));
    // SAYF("input concrete value: %s\n",
    //      Z3_ast_to_string(smt_solver.ctx, input_val));

    // evaluate the query in the model
    Z3_ast  solution;
    Z3_bool successfulEval =
        Z3_model_eval(smt_solver.ctx, z3_m, query, Z3_TRUE, &solution);
    assert(successfulEval && "Failed to evaluate model");
    assert(Z3_get_ast_kind(smt_solver.ctx, solution) == Z3_APP_AST &&
           "Evaluated expression has wrong sort");

    Z3_model_inc_ref(smt_solver.ctx, z3_m);
    res->model = z3_m;
    res->value = Z3_get_bool_value(smt_solver.ctx, solution) == Z3_L_TRUE;
}

static int smt_query_check_light(Z3_ast query, Z3_ast branch_condition)
{
    // 1 -> succeded
#ifdef DEBUG_CHECK_LIGHT
    SAYF("query: \n%s\n", Z3_ast_to_string(smt_solver.ctx, query));
    SAYF("branch condition: \n%s\n\n",
         Z3_ast_to_string(smt_solver.ctx, branch_condition));
#endif

    assert(cached_input_symbol);
    int            i, j, k;
    int            res;
    unsigned long  early_constant1;
    unsigned long  early_constant2;
    Z3_ast         current_expr;
    Z3_ast         tmp_expr;
    testcase_t*    current_testcase;
    testcase_t*    testcase;
    index_group_t* group;
    evaluate_t     eval = {0};

    // L0 -- REUSE
L0:
    if (testcase_list.size < 2)
        // we have only the seed. skip L0
        goto L1;

#ifdef DEBUG_CHECK_LIGHT
    SAYF("Trying L0\n");
#endif

    for (i = 1; i < testcase_list.size; ++i) {
        testcase = &testcase_list.list[i];
        smt_query_evaluate(cached_input_symbol, testcase->z3_formula, query,
                           &eval);
        if (eval.value) {
            SAYF("[check light L0] Query is SAT\n");
            // smt_dump_solution(eval.model);  // no need to reinsert
            Z3_model_dec_ref(smt_solver.ctx, eval.model);
            return 1;
        }
        Z3_model_dec_ref(smt_solver.ctx, eval.model);
    }

    // L1 -- SURGICAL REUSE
L1:
    CLEAR_INDEX_VALUE_QUEUE();
    ast_find_involved_inputs(branch_condition);

#ifdef DEBUG_CHECK_LIGHT
    print_index_and_value_queue();
#endif
    goto L2; // deactivate L2. Need coverage

    if (testcase_list.size < 2)
        // we have only the seed. skip L1
        goto L2;

#ifdef DEBUG_CHECK_LIGHT
    SAYF("Trying L1\n");
#endif

    current_testcase = &testcase_list.list[0];
    current_expr     = current_testcase->z3_formula;
    tmp_expr         = NULL;

    for (i = 1; i < testcase_list.size; ++i) {
        testcase = &testcase_list.list[i];
        tmp_expr = current_expr;
        for (j = 0; j < index_queue.size; ++j) {
            group = &index_queue.index_groups[j];
            for (k = 0; k < group->n; ++k) {
                unsigned int  index = group->indexes[group->n - k - 1];
                unsigned char b     = testcase->testcase[index];

                if (current_testcase->testcase[index] == b)
                    continue;

#ifdef DEBUG_CHECK_LIGHT
                SAYF("inj byte: 0x%x @ %d\n", b, index);
#endif
                tmp_expr =
                    ast_patch_byte(tmp_expr, b, index, current_testcase->len);
            }
        }
#ifdef DEBUG_CHECK_LIGHT
        SAYF("concrete expr: %s\n", Z3_ast_to_string(smt_solver.ctx, tmp_expr));
#endif
        smt_query_evaluate(cached_input_symbol, tmp_expr, query, &eval);
        if (eval.value) {
            SAYF("[check light L1] Query is SAT\n");
            smt_dump_solution(eval.model);
            Z3_model_dec_ref(smt_solver.ctx, eval.model);
            return 1;
        }
        Z3_model_dec_ref(smt_solver.ctx, eval.model);
    }

    // L2 -- INPUT TO STATE
L2:
    if ((res = ast_find_early_constants(branch_condition, &early_constant1,
                                        &early_constant2)) == 0) {
        // no early constant
        goto L3;
    }

#ifdef DEBUG_CHECK_LIGHT
    SAYF("early constants res: 0x%x\n", res);
    SAYF("early constant 1: 0x%lx\n", early_constant1);
    SAYF("early constant 2: 0x%lx\n", early_constant2);

    SAYF("\nTrying L2\n");
#endif

    current_testcase = &testcase_list.list[0];
    current_expr     = current_testcase->z3_formula;
    tmp_expr         = NULL;

    if (res & FOUND_SUB_AND) {
        // early_constant1 is set
        for (j = 0; j < index_queue.size; ++j) {
            group    = &index_queue.index_groups[j];
            tmp_expr = current_expr;
            for (k = 0; k < group->n; ++k) {
                unsigned int  index = group->indexes[group->n - k - 1];
                unsigned char b     = extract_from_long(early_constant1, k);

#ifdef DEBUG_CHECK_LIGHT
                SAYF("inj byte: 0x%x @ %d\n", b, index);
#endif
                if (current_testcase->testcase[index] == b)
                    continue;

                tmp_expr =
                    ast_patch_byte(tmp_expr, b, index, current_testcase->len);
            }
            smt_query_evaluate(cached_input_symbol, tmp_expr, query, &eval);
            if (eval.value) {
                SAYF("[check light L2] Query is SAT\n");
                smt_dump_solution(eval.model);
                Z3_model_dec_ref(smt_solver.ctx, eval.model);
                return 1;
            }
            Z3_model_dec_ref(smt_solver.ctx, eval.model);
        }
    }
    if (res & FOUND_COMPARISON) {
        // early_constant2 is set
        for (j = 0; j < index_queue.size; ++j) {
            group    = &index_queue.index_groups[j];
            tmp_expr = current_expr;
            for (k = 0; k < group->n; ++k) {
                unsigned int  index = group->indexes[group->n - k - 1];
                unsigned char b     = extract_from_long(early_constant2, k);

#ifdef DEBUG_CHECK_LIGHT
                SAYF("inj byte: 0x%x @ %d\n", b, index);
#endif
                if (current_testcase->testcase[index] == b)
                    continue;

                tmp_expr =
                    ast_patch_byte(tmp_expr, b, index, current_testcase->len);
            }
            smt_query_evaluate(cached_input_symbol, tmp_expr, query, &eval);
            if (eval.value) {
                SAYF("[check light L2] Query is SAT\n");
                smt_dump_solution(eval.model);
                Z3_model_dec_ref(smt_solver.ctx, eval.model);
                return 1;
            }
            Z3_model_dec_ref(smt_solver.ctx, eval.model);
        }
    }

    // L3 -- RELAXED INPUT TO STATE
L3:
    // L4 -- CHECKSUM PATCHING
L4:

    return 0;
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

static Z3_ast smt_query_to_z3(Expr* query, uintptr_t is_const)
{
    if (is_const)
        return smt_new_const((uintptr_t)query, 64);

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
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            n   = (uintptr_t)query->op2;
            op1 = Z3_mk_extract(smt_solver.ctx, n - 1, 0, op1);
            op2 = smt_new_const(0, 64 - n);
            r   = Z3_mk_concat(smt_solver.ctx, op2, op1);
            break;
        case SEXT:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const);
            n   = (uintptr_t)query->op2;
            op1 = Z3_mk_extract(smt_solver.ctx, n - 1, 0, op1);
            r   = Z3_mk_sign_ext(smt_solver.ctx, 64 - n, op1);
            break;
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

static Z3_ast ast_find_branch_condition(Z3_ast query)
{
    Z3_ast res = NULL;
    switch (Z3_get_ast_kind(smt_solver.ctx, query)) {
        case Z3_APP_AST: {
            Z3_app       app        = Z3_to_app(smt_solver.ctx, query);
            unsigned     num_fields = Z3_get_app_num_args(smt_solver.ctx, app);
            Z3_func_decl decl       = Z3_get_app_decl(smt_solver.ctx, app);
            Z3_decl_kind decl_kind  = Z3_get_decl_kind(smt_solver.ctx, decl);

            switch (decl_kind) {
                case Z3_OP_AND: {
                    assert(num_fields == 2);
                    Z3_ast branch_condition =
                        Z3_get_app_arg(smt_solver.ctx, app, 0);
                    res = branch_condition;
                    break;
                }
                default: {
                    res = query;
                    break;
                }
            }
            break;
        }
        default: {
            res = query;
            break;
        }
    }
    return res;
}

static void smt_query(Expr* query)
{
    print_expr(query);
    CLEAR_INDEX_VALUE_QUEUE();

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

    SAYF("Running fast checker...\n");
    if (smt_query_check_light(z3_query, ast_find_branch_condition(z3_query)) ==
        0) {
        SAYF("Running slow checker...\n");
        smt_query_check(solver, z3_query, 0);
    }
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
    free_testcase_list(&testcase_list);

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
    if (argc < 3)
        PFATAL("%s seed testcase_folder\n", argv[0]);

    smt_init();
    signal(SIGINT, sig_handler);

    init_testcase_list(&testcase_list);

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

    load_testcase(&testcase_list, argv[1], smt_solver.ctx);
    load_testcase_folder(&testcase_list, argv[2], smt_solver.ctx);

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