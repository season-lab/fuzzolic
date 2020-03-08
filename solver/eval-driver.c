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

#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
static_assert(Z3_VERSION == 487, "This executable requires z3 4.8.7+");

typedef struct {
    uint8_t* data;
    size_t   size;
} Testcase;

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

#define APP(e)    ((Z3_app)e)
#define N_ARGS(e) Z3_get_app_num_args(smt_solver.ctx, APP(e))
#define ARG1(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 0)
#define ARG2(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 1)
#define ARG3(e)   Z3_get_app_arg(smt_solver.ctx, APP(e), 2)
#define ARG(e, i)   Z3_get_app_arg(smt_solver.ctx, APP(e), i)
#define PARAM1(e)                                                              \
    Z3_get_decl_int_parameter(smt_solver.ctx,                                  \
                              Z3_get_app_decl(smt_solver.ctx, APP(e)), 0);
#define PARAM2(e)                                                              \
    Z3_get_decl_int_parameter(smt_solver.ctx,                                  \
                              Z3_get_app_decl(smt_solver.ctx, APP(e)), 1);
#define OP(e) get_op(APP(e))
#define SIZE(e)                                                                \
    Z3_get_bv_sort_size(smt_solver.ctx, Z3_get_sort(smt_solver.ctx, e))

#define FF_MASK(bits) ((2LU << ((bits)-1)) - 1LU)

static inline Z3_decl_kind get_op(Z3_app app)
{
    Z3_func_decl decl = Z3_get_app_decl(smt_solver.ctx, app);
    return Z3_get_decl_kind(smt_solver.ctx, decl);
}

static void print_z3_ast(Z3_ast e)
{
    Z3_set_ast_print_mode(smt_solver.ctx, Z3_PRINT_LOW_LEVEL);
    const char* z3_query_str = Z3_ast_to_string(smt_solver.ctx, e);
    SAYF("\n%s\n", z3_query_str);
}

static Testcase testcase;

static inline void load_testcase(const char* path)
{
    printf("Loading testcase: %s\n", path);
    char  data[1024 * 100] = {0};
    FILE* fp               = fopen(path, "r");
    int   r                = fread(&data, 1, sizeof(data), fp);
    fclose(fp);
    if (r == sizeof(data)) {
        PFATAL("Testcase is too large\n");
    }
    printf("Loaded %d bytes from testcase: %s\n", r, path);
    assert(r > 0);
    testcase.data = malloc(r);
    testcase.size = r;
    memmove(testcase.data, &data, r);
}

static inline unsigned long compute_time_usec(struct timeval* start,
                                              struct timeval* end)
{
    return ((end->tv_sec - start->tv_sec) * 1000000 + end->tv_usec -
            start->tv_usec);
}

static inline void usage(char* filename)
{
    fprintf(stderr, "wrong argv. usage:\n%s query_filename seed\n", filename);
    exit(1);
}

unsigned long z3fuzz_evaluate_expression_z3(Z3_context ctx,
                                            Z3_ast query)
{
    // evaluate query using [input <- input_val] as interpretation

    // build a model and assign an interpretation for the input symbols
    unsigned long  res;
    Z3_sort        sort = Z3_mk_bv_sort(ctx, 8);
    Z3_model       z3_m = Z3_mk_model(ctx);
    Z3_model_inc_ref(ctx, z3_m);

    unsigned i;
    for (i = 0; i < testcase.size; ++i) {
        Z3_ast  e    = Z3_mk_unsigned_int64(ctx, testcase.data[i], sort);
        char*   name = malloc(16);
        snprintf(name, 16, "input_%u", i);
        Z3_symbol s = Z3_mk_string_symbol(ctx, name);
        free(name);
        Z3_func_decl decl  = Z3_mk_func_decl(ctx, s, 0, NULL, sort);
        Z3_add_const_interp(ctx, z3_m, decl, e);
    }

    // evaluate the query in the model
    Z3_ast  solution;
    Z3_bool successfulEval =
        Z3_model_eval(ctx, z3_m, query, Z3_TRUE, &solution);
    assert(successfulEval && "Failed to evaluate model");

    Z3_model_dec_ref(ctx, z3_m);
    if (Z3_get_ast_kind(ctx, solution) == Z3_NUMERAL_AST) {
        Z3_bool successGet = Z3_get_numeral_uint64(ctx, solution, &res);
        assert(successGet == Z3_TRUE &&
               "z3fuzz_evaluate_expression_z3() failed to get "
               "constant");
    } else
        res = Z3_get_bool_value(ctx, solution) == Z3_L_TRUE ? 1UL : 0UL;
    Z3_dec_ref(ctx, solution);
    return res;
}

#include "eval.c"

typedef dict__cached_value_t eval_value_cache_t;

uintptr_t local_cache_hits2 = 0;
uintptr_t local_cache_lookups2 = 0;

static inline unsigned long
__evaluate_expression(Z3_context ctx, Z3_ast value, Z3_ast* values,
                      long*                 blacklisted_inputs,
                      unsigned              blacklisted_inputs_size,
                      dict__cached_value_t* local_cache, int use_global_cache)
{
    unsigned long value_hash = Z3_get_ast_id(ctx, value);
    unsigned long res, tmp1, tmp2;
    unsigned      has_cache = 0;

    cached_value_t* local_cached_value =
        dict_get_ref__cached_value_t(local_cache, value_hash);
    local_cache_lookups2++;
    if (local_cached_value != NULL && local_cached_value->valid) {
        res       = local_cached_value->value;
        has_cache = 1;
        local_cache_hits2++;
    }

    if (has_cache) {
        return res;
    }

    // printf("ast kind: %u\n", Z3_get_ast_kind(ctx, value));
    switch (Z3_get_ast_kind(ctx, value)) {
        case Z3_APP_AST: {
            Z3_app       app       = Z3_to_app(ctx, value);
            Z3_func_decl decl      = Z3_get_app_decl(ctx, app);
            Z3_decl_kind decl_kind = Z3_get_decl_kind(ctx, decl);
            // printf("decl kind: %u\n", decl_kind);

            switch (decl_kind) {
                case Z3_OP_UNINTERPRETED: {
                    Z3_symbol s = Z3_get_decl_name(ctx, decl);
#if 0
                    int       symbol_index = Z3_get_symbol_int(ctx, s);
                    Z3_bool   successGet =
                        Z3_get_numeral_uint64(ctx, values[symbol_index],
#if Z3_VERSION <= 451
                                              (long long unsigned int*)&res
#else
                                              (uint64_t*)&res
#endif
                        );
                    assert(successGet == Z3_TRUE &&
                           "z3fuzz_evaluate_expression() failed to get "
                           "constant (symbol)");
#else
                    const char* s_name      = Z3_get_symbol_string(ctx, s);
                    int index = strtol(s_name + 6, NULL, 10);
                    res = testcase.data[index];
#endif
                    break;
                }
                // booleans
                case Z3_OP_EQ: {

                    Z3_ast child1 = Z3_get_app_arg(ctx, app, 0);
                    Z3_ast child2 = Z3_get_app_arg(ctx, app, 1);

                    Z3_sort  child_sort = Z3_get_sort(ctx, child1);
                    unsigned child_sort_size =
                        Z3_get_sort_kind(ctx, child_sort) == Z3_BV_SORT
                            ? Z3_get_bv_sort_size(ctx, child_sort)
                            : 0;

                    if (child_sort_size > 64) {
#ifdef PRINT_WARNINGS
                        printf("z3fuzz_evaluate_expression() WARNING [EQ]: "
                               "extract "
                               "child with sort_size > 64. Using Z3\n");
#endif
                        res = z3fuzz_evaluate_expression_z3(ctx, value);
                    } else {
                        tmp1 = __evaluate_expression(
                            ctx, child1, values, blacklisted_inputs,
                            blacklisted_inputs_size, local_cache,
                            use_global_cache);
                        tmp2 = __evaluate_expression(
                            ctx, child2, values, blacklisted_inputs,
                            blacklisted_inputs_size, local_cache,
                            use_global_cache);
                        res = tmp1 == tmp2 ? 1 : 0;
                    }
                    break;
                }
                case Z3_OP_NOT: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    assert((tmp1 == 1 || tmp1 == 0) &&
                           "z3fuzz_evaluate_expression() wrong sort [not]");
                    res = tmp1 == 1 ? 0 : 1;
                    break;
                }
                case Z3_OP_ULT: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = tmp1 < tmp2 ? 1 : 0;
                    break;
                }
                case Z3_OP_ULEQ: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = tmp1 <= tmp2 ? 1 : 0;
                    break;
                }
                case Z3_OP_SLT: {
                    Z3_sort value_sort = Z3_get_sort(
                        ctx, Z3_get_app_arg(ctx, app, 0));
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    switch (value_sort_size) {
                        case 8:
                            res = (unsigned long)((char)tmp1 < (char)tmp2 ? 1
                                                                          : 0);
                            break;
                        case 16:
                            res =
                                (unsigned long)((short)tmp1 < (short)tmp2 ? 1
                                                                          : 0);
                            break;
                        case 32:
                            res =
                                (unsigned long)((int)tmp1 < (int)tmp2 ? 1 : 0);
                            break;
                        case 64:
                            res = (unsigned long)((long)tmp1 < (long)tmp2 ? 1
                                                                          : 0);
                            break;
                        default:
                            assert(0 && "z3fuzz_evaluate_expression() "
                                        "unexpected size [slt]");
                    }
                    break;
                }
                case Z3_OP_SLEQ: {
                    Z3_sort value_sort = Z3_get_sort(
                        ctx, Z3_get_app_arg(ctx, app, 0));
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    switch (value_sort_size) {
                        case 8:
                            res = (unsigned long)((char)tmp1 <= (char)tmp2 ? 1
                                                                           : 0);
                            break;
                        case 16:
                            res =
                                (unsigned long)((short)tmp1 <= (short)tmp2 ? 1
                                                                           : 0);
                            break;
                        case 32:
                            res =
                                (unsigned long)((int)tmp1 <= (int)tmp2 ? 1 : 0);
                            break;
                        case 64:
                            res = (unsigned long)((long)tmp1 <= (long)tmp2 ? 1
                                                                           : 0);
                            break;
                        default:
                            assert(0 && "z3fuzz_evaluate_expression() "
                                        "unexpected size [sleq]");
                    }
                    break;
                }
                case Z3_OP_UGT: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = tmp1 > tmp2 ? 1 : 0;
                    break;
                }
                case Z3_OP_UGEQ: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = tmp1 >= tmp2 ? 1 : 0;
                    break;
                }
                case Z3_OP_SGT: {
                    Z3_sort value_sort = Z3_get_sort(
                        ctx, Z3_get_app_arg(ctx, app, 0));
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);

                    switch (value_sort_size) {
                        case 8:
                            res = (unsigned long)((char)tmp1 > (char)tmp2 ? 1
                                                                          : 0);
                            break;
                        case 16:
                            res =
                                (unsigned long)((short)tmp1 > (short)tmp2 ? 1
                                                                          : 0);
                            break;
                        case 32:
                            res =
                                (unsigned long)((int)tmp1 > (int)tmp2 ? 1 : 0);
                            break;
                        case 64:
                            res = (unsigned long)((long)tmp1 > (long)tmp2 ? 1
                                                                          : 0);
                            break;
                        default:
                            assert(0 && "z3fuzz_evaluate_expression() "
                                        "unexpected size [sgt]");
                    }
                    break;
                }
                case Z3_OP_SGEQ: {
                    Z3_sort value_sort = Z3_get_sort(
                        ctx, Z3_get_app_arg(ctx, app, 0));
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    switch (value_sort_size) {
                        case 8:
                            res = (unsigned long)((char)tmp1 >= (char)tmp2 ? 1
                                                                           : 0);
                            break;
                        case 16:
                            res =
                                (unsigned long)((short)tmp1 >= (short)tmp2 ? 1
                                                                           : 0);
                            break;
                        case 32:
                            res =
                                (unsigned long)((int)tmp1 >= (int)tmp2 ? 1 : 0);
                            break;
                        case 64:
                            res = (unsigned long)((long)tmp1 >= (long)tmp2 ? 1
                                                                           : 0);
                            break;
                        default:
                            assert(0 && "z3fuzz_evaluate_expression() "
                                        "unexpected size [sgeq]");
                    }
                    break;
                }
                case Z3_OP_AND: {
                    unsigned num_args = Z3_get_app_num_args(ctx, app);
                    res               = 1;

                    unsigned i;
                    for (i = 0; i < num_args; ++i) {
                        tmp1 = __evaluate_expression(
                            ctx, Z3_get_app_arg(ctx, app, i), values,
                            blacklisted_inputs, blacklisted_inputs_size,
                            local_cache, use_global_cache);
                        assert((tmp1 == 1 || tmp1 == 0) &&
                               "z3fuzz_evaluate_expression() wrong sort [and]");
                        if (tmp1 == 0) {
                            res = 0;
                            break;
                        }
                    }
                    break;
                }
                case Z3_OP_OR: {
                    unsigned num_args = Z3_get_app_num_args(ctx, app);
                    res               = 0;
                    unsigned i;
                    for (i = 0; i < num_args; ++i) {
                        tmp1 = __evaluate_expression(
                            ctx, Z3_get_app_arg(ctx, app, i), values,
                            blacklisted_inputs, blacklisted_inputs_size,
                            local_cache, use_global_cache);
                        assert((tmp1 == 1 || tmp1 == 0) &&
                               "z3fuzz_evaluate_expression() wrong sort [or]");
                        if (tmp1 == 1) {
                            res = 1;
                            break;
                        }
                    }
                    break;
                }
                // arithmetics
                case Z3_OP_BNEG: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = -tmp1;
                    res = res & value_mask;
                    break;
                }
                case Z3_OP_BNOT: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = ~tmp1;
                    res = res & value_mask;
                    break;
                }
                case Z3_OP_BADD: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    unsigned num_args = Z3_get_app_num_args(ctx, app);
                    res               = 0;
                    unsigned i;
                    for (i = 0; i < num_args; ++i) {
                        tmp1 = __evaluate_expression(
                            ctx, Z3_get_app_arg(ctx, app, i), values,
                            blacklisted_inputs, blacklisted_inputs_size,
                            local_cache, use_global_cache);
                        res += tmp1;
                    }
                    res = res & value_mask;
                    break;
                }
                case Z3_OP_BSUB: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = tmp1 - tmp2;
                    res = res & value_mask;
                    break;
                }
                case Z3_OP_BMUL: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    unsigned num_args = Z3_get_app_num_args(ctx, app);
                    res               = 1;
                    unsigned i;
                    for (i = 0; i < num_args; ++i) {
                        tmp1 = __evaluate_expression(
                            ctx, Z3_get_app_arg(ctx, app, i), values,
                            blacklisted_inputs, blacklisted_inputs_size,
                            local_cache, use_global_cache);
                        res *= tmp1;
                    }

                    res = res & value_mask;
                    break;
                }
                case Z3_OP_BSREM:
                case Z3_OP_BSREM_I: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    if (tmp2 == 0) {
#ifdef PRINT_WARNINGS
                        Z3FUZZ_LOG("z3fuzz_evaluate_expression() WARNING - "
                                   "bsrem div by zero\n");
#endif
#ifdef DUMP_DIV0_PROOFS
                        char     var_name[128];
                        unsigned n;
                        n = snprintf(var_name, sizeof(var_name),
                                     "tests/div0_proof_%lu",
                                     fuzzy_stats.num_warnings_div0);
                        assert(n > 0 && n < sizeof(var_name) &&
                               "symbol name too long");

                        z3fuzz_dump_proof(ctx, var_name, values,
                                          ctx->testcases.data[0].len);
#endif

                        // compliance to Z3: division by zero yields -1
                        res = -1;
                        break;
                    }

                    switch (value_sort_size) {
                        case 8:
                            res = (unsigned long)((char)tmp1 % (char)tmp2);
                            break;
                        case 16:
                            res = (unsigned long)((short)tmp1 % (short)tmp2);
                            break;
                        case 32:
                            res = (unsigned long)((int)tmp1 % (int)tmp2);
                            break;
                        case 64:
                            res = (unsigned long)((long)tmp1 % (long)tmp2);
                            break;
                        default:
                            assert(0 && "z3fuzz_evaluate_expression() "
                                        "unexpected size [srem]");
                    }
                    res &= value_mask;
                    break;
                }
                case Z3_OP_BUREM:
                case Z3_OP_BUREM_I: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    if (tmp2 == 0) {
#ifdef PRINT_WARNINGS
                        Z3FUZZ_LOG("z3fuzz_evaluate_expression() WARNING - "
                                   "burem div by zero\n");
#endif
#ifdef DUMP_DIV0_PROOFS
                        char     var_name[128];
                        unsigned n;
                        n = snprintf(var_name, sizeof(var_name),
                                     "tests/div0_proof_%lu",
                                     fuzzy_stats.num_warnings_div0);
                        assert(n > 0 && n < sizeof(var_name) &&
                               "symbol name too long");

                        z3fuzz_dump_proof(ctx, var_name, values,
                                          ctx->testcases.data[0].len);
#endif

                        // compliance to Z3: division by zero yields -1
                        res = -1;
                        break;
                    }
                    res = tmp1 % tmp2;
                    break;
                }
                case Z3_OP_BSDIV:
                case Z3_OP_BSDIV_I: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    if (tmp2 == 0) {
#ifdef PRINT_WARNINGS
                        Z3FUZZ_LOG("z3fuzz_evaluate_expression() WARNING - "
                                   "bsdiv div by zero\n");
#endif
#ifdef DUMP_DIV0_PROOFS
                        char     var_name[128];
                        unsigned n;
                        n = snprintf(var_name, sizeof(var_name),
                                     "tests/div0_proof_%lu",
                                     fuzzy_stats.num_warnings_div0);
                        assert(n > 0 && n < sizeof(var_name) &&
                               "symbol name too long");

                        z3fuzz_dump_proof(ctx, var_name, values,
                                          ctx->testcases.data[0].len);
#endif

                        // compliance to Z3: division by zero yields -1
                        res = -1;
                        break;
                    }

                    switch (value_sort_size) {
                        case 8:
                            res = (unsigned long)((char)tmp1 / (char)tmp2);
                            break;
                        case 16:
                            res = (unsigned long)((short)tmp1 / (short)tmp2);
                            break;
                        case 32:
                            res = (unsigned long)((int)tmp1 / (int)tmp2);
                            break;
                        case 64:
                            res = (unsigned long)((long)tmp1 / (long)tmp2);
                            break;
                        default:
                            assert(0 && "z3fuzz_evaluate_expression() "
                                        "unexpected size [sdiv]");
                    }
                    res = res & value_mask;
                    break;
                }
                case Z3_OP_BUDIV:
                case Z3_OP_BUDIV_I: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    if (tmp2 == 0) {
#ifdef PRINT_WARNINGS
                        Z3FUZZ_LOG("z3fuzz_evaluate_expression() WARNING - "
                                   "budiv div by zero\n");
#endif
#ifdef DUMP_DIV0_PROOFS
                        char     var_name[128];
                        unsigned n;
                        n = snprintf(var_name, sizeof(var_name),
                                     "tests/div0_proof_%lu",
                                     fuzzy_stats.num_warnings_div0);
                        assert(n > 0 && n < sizeof(var_name) &&
                               "symbol name too long");

                        z3fuzz_dump_proof(ctx, var_name, values,
                                          ctx->testcases.data[0].len);
#endif

                        // compliance to Z3: division by zero yields -1
                        res = -1;
                        break;
                    }
                    res = tmp1 / tmp2;
                    break;
                }
                case Z3_OP_BAND: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    unsigned num_args = Z3_get_app_num_args(ctx, app);
                    res               = value_mask;
                    unsigned i;
                    for (i = 0; i < num_args; ++i) {
                        tmp1 = __evaluate_expression(
                            ctx, Z3_get_app_arg(ctx, app, i), values,
                            blacklisted_inputs, blacklisted_inputs_size,
                            local_cache, use_global_cache);
                        res &= tmp1;
                    }
                    break;
                }
                case Z3_OP_BOR: {
                    unsigned num_args = Z3_get_app_num_args(ctx, app);
                    res               = 0;
                    unsigned i;
                    for (i = 0; i < num_args; ++i) {
                        tmp1 = __evaluate_expression(
                            ctx, Z3_get_app_arg(ctx, app, i), values,
                            blacklisted_inputs, blacklisted_inputs_size,
                            local_cache, use_global_cache);
                        res |= tmp1;
                    }
                    break;
                }
                case Z3_OP_BXOR: {
                    unsigned num_args = Z3_get_app_num_args(ctx, app);
                    res               = 0;
                    unsigned i;
                    for (i = 0; i < num_args; ++i) {
                        tmp1 = __evaluate_expression(
                            ctx, Z3_get_app_arg(ctx, app, i), values,
                            blacklisted_inputs, blacklisted_inputs_size,
                            local_cache, use_global_cache);
                        res ^= tmp1;
                    }
                    break;
                }
                case Z3_OP_BSHL: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);
                    unsigned long value_mask =
                        (2LU << (value_sort_size - 1LU)) - 1LU;

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = tmp1 << tmp2;
                    res &= value_mask;
                    break;
                }
                case Z3_OP_BASHR: {
                    Z3_sort  value_sort = Z3_get_sort(ctx, value);
                    unsigned value_sort_size =
                        Z3_get_bv_sort_size(ctx, value_sort);

                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    switch (value_sort_size) {
                        case 8:
                            res = (unsigned long)((char)tmp1 >> (char)tmp2);
                            break;
                        case 16:
                            res = (unsigned long)((short)tmp1 >> (short)tmp2);
                            break;
                        case 32:
                            res = (unsigned long)((int)tmp1 >> (int)tmp2);
                            break;
                        case 64:
                            res = (unsigned long)((long)tmp1 >> (long)tmp2);
                            break;
                        default:
                            assert(0 && "z3fuzz_evaluate_expression() "
                                        "unexpected size [ashr]");
                    }
                    break;
                }
                case Z3_OP_BLSHR: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    tmp2 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 1), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = tmp1 >> tmp2;
                    break;
                }
                case Z3_OP_ZERO_EXT: {
                    tmp1 = __evaluate_expression(
                        ctx, Z3_get_app_arg(ctx, app, 0), values,
                        blacklisted_inputs, blacklisted_inputs_size,
                        local_cache, use_global_cache);
                    res = tmp1;
                    break;
                }
                case Z3_OP_SIGN_EXT: {
                    Z3_ast   child      = Z3_get_app_arg(ctx, app, 0);
                    Z3_sort  child_sort = Z3_get_sort(ctx, child);
                    unsigned child_sort_size =
                        Z3_get_bv_sort_size(ctx, child_sort);

                    tmp1 = __evaluate_expression(
                        ctx, child, values, blacklisted_inputs,
                        blacklisted_inputs_size, local_cache, use_global_cache);
                    unsigned long n =
                        Z3_get_decl_int_parameter(ctx, decl, 0);
                    if (tmp1 & (1 << (child_sort_size - 1))) {
                        // negative number
                        tmp2 = (2 << (n - 1)) - 1; // 1..1 mask for new bits
                        tmp2 = tmp2 << child_sort_size;
                        tmp1 |= tmp2;
                    }
                    res = tmp1;
                    break;
                }
                case Z3_OP_CONCAT: {
                    res               = 0;
                    unsigned size     = 0;
                    unsigned num_args = Z3_get_app_num_args(ctx, app);
                    int      i;
                    for (i = num_args - 1; i >= 0; --i) {
                        Z3_ast   arg      = Z3_get_app_arg(ctx, app, i);
                        Z3_sort  arg_sort = Z3_get_sort(ctx, arg);
                        unsigned arg_sort_size =
                            Z3_get_bv_sort_size(ctx, arg_sort);

                        tmp1 = __evaluate_expression(
                            ctx, arg, values, blacklisted_inputs,
                            blacklisted_inputs_size, local_cache,
                            use_global_cache);

                        res |= (tmp1 << size);
                        size += arg_sort_size;

                        assert(size <= 64 &&
                               "z3fuzz_evaluate_expression() size too big");
                    }
                    break;
                }
                case Z3_OP_EXTRACT: {
                    unsigned long hig =
                        Z3_get_decl_int_parameter(ctx, decl, 0);
                    unsigned long low =
                        Z3_get_decl_int_parameter(ctx, decl, 1);

                    Z3_ast   child      = Z3_get_app_arg(ctx, app, 0);
                    Z3_sort  child_sort = Z3_get_sort(ctx, child);
                    unsigned child_sort_size =
                        Z3_get_bv_sort_size(ctx, child_sort);

                    if (child_sort_size > 64) {
#ifdef PRINT_WARNINGS
                        printf("z3fuzz_evaluate_expression() WARNING: extract "
                               "child with sort_size > 64. Using Z3\n");
#endif
                        res = z3fuzz_evaluate_expression_z3(ctx, value);
                    } else {
                        tmp1 = __evaluate_expression(
                            ctx, child, values, blacklisted_inputs,
                            blacklisted_inputs_size, local_cache,
                            use_global_cache);

                        res = (tmp1 >> low) & ((2UL << (hig - low)) - 1UL);
                    }
                    break;
                }
                case Z3_OP_ITE: {
                    Z3_ast cond    = Z3_get_app_arg(ctx, app, 0);
                    Z3_ast iftrue  = Z3_get_app_arg(ctx, app, 1);
                    Z3_ast iffalse = Z3_get_app_arg(ctx, app, 2);
                    tmp1           = __evaluate_expression(
                        ctx, cond, values, blacklisted_inputs,
                        blacklisted_inputs_size, local_cache, use_global_cache);
                    res = __evaluate_expression(ctx, tmp1 ? iftrue : iffalse,
                                                values, blacklisted_inputs,
                                                blacklisted_inputs_size,
                                                local_cache, use_global_cache);
                    break;
                }
                case Z3_OP_TRUE: {
                    res = 1;
                    break;
                }
                case Z3_OP_FALSE: {
                    res = 0;
                    break;
                }
                default:
                    assert(0);
                    break;
            }
            break;
        }
        case Z3_NUMERAL_AST: {
            Z3_bool successGet =
                Z3_get_numeral_uint64(ctx, value,
#if Z3_VERSION <= 451
                                      (long long unsigned int*)&res
#else
                                      (uint64_t*)&res
#endif
                );
            assert(successGet == Z3_TRUE &&
                   "z3fuzz_evaluate_expression() failed to get constant");
            break;
        }
        default: {
            assert(0 && "z3fuzz_evaluate_expression() unknown ast_kind");
        }
    }

    cached_value_t cache_el;
    cache_el.valid = 1;
    cache_el.value = res;
    dict_set__cached_value_t(local_cache, value_hash, cache_el);
    return res;
}

unsigned long z3fuzz_evaluate_expression(Z3_context ctx, Z3_ast value)
{
    dict__cached_value_t tmp;
    dict_init__cached_value_t(&tmp);
    unsigned long res =
        __evaluate_expression(ctx, value, NULL, NULL, 0, &tmp, 0);
    dict_free__cached_value_t(&tmp, NULL);
    return res;
}

#define NUM_ITERATIONS 1000

int main(int argc, char* argv[])
{
    if (argc < 2)
        usage(argv[0]);

    char*          query_filename = argv[1];
    char*          seed_filename  = argv[2];
    char*          tests_dir      = argc > 3 ? argv[3] : NULL;
    Z3_config      cfg            = Z3_mk_config();
    Z3_context     ctx            = Z3_mk_context(cfg);
    Z3_ast         query;
    Z3_ast*        str0_symbols; 
    Z3_ast*        str1_symbols;
    char           var_name[128];
    Z3_sort        bsort = Z3_mk_bv_sort(ctx, 8);
    struct timeval stop, start;
    unsigned long  elapsed_time_z3 = 0, elapsed_time_fuzzolic = 0, elapsed_time_fast = 0;
    unsigned long  num_queries;
    unsigned long  res1, res2;
    unsigned int   i;
    int            n;

    load_testcase(seed_filename);

    str0_symbols = malloc(sizeof(Z3_ast) * testcase.size);
    str1_symbols = malloc(sizeof(Z3_ast) * testcase.size);
    uint8_t* model = malloc(sizeof(uint8_t) * testcase.size);
    for (i = 0; i < testcase.size; ++i) {
        n = snprintf(var_name, sizeof(var_name), "input_%u", i);
        assert(n > 0 && n < sizeof(var_name) && "symbol name too long");
        Z3_symbol s    = Z3_mk_string_symbol(ctx, var_name);
        Z3_ast    s_bv = Z3_mk_const(ctx, s, bsort);
        str0_symbols[i] = s_bv;

        n = snprintf(var_name, sizeof(var_name), "k!%u", i);
        assert(n > 0 && n < sizeof(var_name) && "symbol name too long");
        s    = Z3_mk_string_symbol(ctx, var_name);
        s_bv = Z3_mk_const(ctx, s, bsort);
        str1_symbols[i] = s_bv;

        model[i] = testcase.data[i];
    }

    Z3_ast_vector queries =
        Z3_parse_smtlib2_file(ctx, query_filename, 0, 0, 0, 0, 0, 0);
    Z3_ast_vector_inc_ref(ctx, queries);

    num_queries = Z3_ast_vector_size(ctx, queries);
    assert(num_queries == 1 && "only one query is allowed");
    query                   = Z3_ast_vector_get(ctx, queries, 0);
    query = Z3_substitute(ctx, query, testcase.size, str1_symbols, str0_symbols);

    smt_solver.ctx = ctx;

    uintptr_t value;
    uint8_t from_cache;

    dict__uint64_t model_others;
    dict_init__uint64_t(&model_others);

    blacklist_inputs = malloc(sizeof(dict__uint64_t));
    dict_init__uint64_t(blacklist_inputs);

    if (!global_cache) {
        global_cache = malloc(sizeof(dict__uint64_t));
        dict_init__uint64_t(global_cache);
    }

    get_inputs_expr(query);

    for (i = 0; i < NUM_ITERATIONS; ++i) {
        n = snprintf(var_name, sizeof(var_name), "iteration %d/%d", i,
                     NUM_ITERATIONS);
        assert(n > 0 && n < sizeof(var_name) && "var name too long");
        printf("%s\n", var_name);

        gettimeofday(&start, NULL);
        res2 = z3fuzz_evaluate_expression_z3(ctx, query);
        gettimeofday(&stop, NULL);
        elapsed_time_z3 += compute_time_usec(&start, &stop);

        gettimeofday(&start, NULL);
        res2 = z3fuzz_evaluate_expression(ctx, query);
        gettimeofday(&stop, NULL);
        elapsed_time_fast += compute_time_usec(&start, &stop);

        gettimeofday(&start, NULL);
        res1 = conc_eval_uint64(model, testcase.size, &model_others, query, &value, &from_cache);
        gettimeofday(&stop, NULL);
        elapsed_time_fuzzolic += compute_time_usec(&start, &stop);

        // printf("res1=%lu res2=%lu\n", res1, res2);
        assert(res1 == res2 && "bug in evaluate!");
    }

    printf("Elapsed time fuzzolic:\t%ld usec\n", elapsed_time_fuzzolic);
    printf("Elapsed time z3:\t%ld usec\n", elapsed_time_z3);
    printf("Elapsed time fuzzy:\t%ld usec\n", elapsed_time_fast);

    printf("Fuzzolic:\t hits=%lu lookups=%lu\n", local_cache_hits, local_cache_lookups);
    printf("Fuzzy:\t hits=%lu lookups=%lu\n", local_cache_hits2, local_cache_lookups2);

    return 0;
}