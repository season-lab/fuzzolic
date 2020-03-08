
#define XXH_STATIC_LINKING_ONLY
#include "xxHash/xxhash.h"

#define DICT_DATA_T uint64_t
#include "dict.h"

#define DICT_DATA_T Z3_ast
#include "dict.h"

typedef struct cached_value_t {
    unsigned long value;
    unsigned      valid;
} cached_value_t;

#define DICT_DATA_T cached_value_t
#define DICT_NO_GET
#include "dict.h"
#undef DICT_NO_GET

dict__uint64_t* ast_to_inputs = NULL;

static uintptr_t hash_str(const char* s, size_t n)
{
    XXH32_state_t state;
    XXH32_reset(&state, 0); // seed = 0
    XXH32_update(&state, s, n);
    return XXH32_digest(&state);
}

#define OPERATION(a, b, size, operator, res)                                   \
        switch (size) {                                                        \
            case 8:                                                            \
                res = (unsigned long)((int8_t)a operator(int8_t) b);           \
                break;                                                         \
            case 16:                                                           \
                res = (unsigned long)((int16_t)a operator(int16_t) b);         \
                break;                                                         \
            case 32:                                                           \
                res = (unsigned long)((int32_t)a operator(int32_t) b);         \
                break;                                                         \
            case 64:                                                           \
                res = (unsigned long)((int64_t)a operator(int64_t) b);         \
                break;                                                         \
            default:                                                           \
                assert(0 && "unexpected size [slt]");                          \
        }

static dict__uint64_t* blacklist_inputs = NULL;
static dict__uint64_t* global_cache     = NULL;

static uintptr_t global_cache_hits    = 0;
static uintptr_t global_cache_lookups = 0;
static uintptr_t local_cache_hits     = 0;
static uintptr_t local_cache_lookups  = 0;

static uintptr_t conc_eval(uint8_t* m, size_t n, dict__uint64_t* m_others,
                           Z3_ast e, dict__cached_value_t* cache, uint8_t* from_cache)
{
    Z3_context ctx = smt_solver.ctx;
    uintptr_t  res;
    uintptr_t  arg1 = 0, arg2 = 0, arg3 = 0;

    uintptr_t hash = Z3_get_ast_id(ctx, e);
    assert(hash);

    cached_value_t* local_cached_value =
        dict_get_ref__cached_value_t(cache, hash);
    local_cache_lookups++;
    if (local_cached_value != NULL && local_cached_value->valid) {
        res       = local_cached_value->value;
        *from_cache = 1;
        local_cache_hits++;
        return res;
    }

#if 0
    int rh = dict_contains__uint64_t(cache, hash, &arg2);
    local_cache_lookups++;
    if (rh == TRUE) {
#if 0
        printf("Using local cache: ");
        print_z3_ast_internal(e, 0, 0);
        printf("\n");
#endif
        local_cache_hits++;
        *from_cache = 1;
        return arg2;
    }
#endif

    int skip_global_cache = 0;
#if 1
    GHashTable* inputs = (GHashTable*)dict_get__uint64_t(ast_to_inputs, hash);

    // print_z3_ast(e);

    assert(inputs != NULL);
    assert(blacklist_inputs);
    assert(global_cache);

    GHashTableIter iter;
    gpointer       key, value;
    g_hash_table_iter_init(&iter, inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        if (dict_contains__uint64_t(blacklist_inputs, (uint64_t)key, NULL)) {
#if 0
            printf("Skipping global cache due to blacklist\n");
#endif
            skip_global_cache = 1;
            break;
        }
    }
    if (!skip_global_cache) {
        global_cache_lookups += 1;
        int rh = dict_contains__uint64_t(global_cache, hash, &arg2);
        if (rh == TRUE) {
#if 0
            printf("Using global cache: ");
            print_z3_ast_internal(e, 0, 0);
            printf("\n");
#endif
            *from_cache = 1;
            global_cache_hits += 1;
            return arg2;
        }
    }
#endif

#if 0
    printf("Computing expression: ");
    print_z3_ast_internal(e, 0, 0);
    printf("\n");
#endif
#if 0
    g_hash_table_iter_init(&iter, blacklist_inputs);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        printf("Blacklist: input_%lu\n", (uintptr_t) key );
    }
#endif

    switch (Z3_get_ast_kind(ctx, e)) {

        case Z3_APP_AST: {

            Z3_app       app          = Z3_to_app(ctx, e);
            Z3_func_decl decl         = Z3_get_app_decl(ctx, app);
            Z3_decl_kind decl_kind    = Z3_get_decl_kind(ctx, decl);
#if 0
            unsigned     num_operands = N_ARGS(e);
            Z3_sort      sort         = Z3_get_sort(smt_solver.ctx, e);
            Z3_sort_kind sort_kind    = Z3_get_sort_kind(ctx, sort);

            if (sort_kind != Z3_BOOL_SORT) {
                if (SIZE(e) > 64) {
                    res = (uint64_t)z3fuzz_evaluate_expression_z3(ctx, e);
                    break;
                }
            } else {
                int fallback_z3 = 0;
                for (size_t i = 0; i < num_operands; i++) {
                    if (Z3_get_sort_kind(ctx, Z3_get_sort(ctx, ARG(e, i))) ==
                        Z3_BOOL_SORT) {
                        continue;
                    }
                    if (SIZE(ARG(e, i)) > 64) {
                        fallback_z3 = 1;
                        break;
                    }
                }
                if (fallback_z3) {
                    res = (uint64_t)z3fuzz_evaluate_expression_z3(ctx, e);
                    break;
                }
            }
#endif
#if 0
            if (num_operands == 0) {
                // do nothing here
            } else if (num_operands == 1) {
                arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
            } else if (num_operands == 2) {
                if (OP(e) == Z3_OP_CONCAT || OP(e) == Z3_OP_OR || OP(e) == Z3_OP_AND) {
                    // do nothing
                } else {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                }
            } else if (num_operands == 3) {
                if (OP(e) == Z3_OP_CONCAT || OP(e) == Z3_OP_BADD || OP(e) == Z3_OP_ITE) {
                    // do nothing here
                } else {
                    ABORT("Expr with more than two operands. Not yet supported");
                }
            } else {
                if (OP(e) != Z3_OP_AND && OP(e) != Z3_OP_BADD &&
                    OP(e) != Z3_OP_CONCAT) {
                    print_z3_ast(e);
                    ABORT(
                        "Expr with more than three operands. Not yet supported");
                }
            }
#endif
#if 0
            printf("arg1=%lx arg2=%lx arg3=%lx - expr: ", arg1, arg2, arg3);
            print_z3_ast_internal(e, 0, 0);
            printf("\n\n");
#endif
            switch (decl_kind) {

                case Z3_OP_UNINTERPRETED: {
                    Z3_symbol   symbol = Z3_get_decl_name(ctx, decl);
                    const char* s      = Z3_get_symbol_string(ctx, symbol);
                    if (s[0] == 'i' && s[1] == 'n') {
                        size_t index = strtol(s + 6, NULL, 10);
                        assert(index < n);
                        // printf("Input_%lu: %u\n", index, m[index]);
                        res = m[index];
                    } else if (s[0] == 's' && (s[1] == '_' || s[1] == 'v')) {
                        // printf("SLoad: %s %s\n", s, s+6);
                        size_t index = hash_str(s, strlen(s));
                        int    rh = dict_contains__uint64_t(m_others, index, &arg2);
                        if (!rh) {
                            printf("S/VLoad: %s\n", s);
                        }
                        assert(rh);
                        res = arg2;
                    } else {
                        printf("Symbol: %s\n", s);
                        ABORT();
                    }
                    break;
                }

                case Z3_OP_TRUE: {
                    *from_cache = 0;
                    res = 1;
                    break;
                }
                case Z3_OP_FALSE: {
                    *from_cache = 0;
                    res = 0;
                    break;
                }

                case Z3_OP_EQ: {
                    Z3_ast child1 = Z3_get_app_arg(ctx, app, 0);
                    Z3_ast child2 = Z3_get_app_arg(ctx, app, 1);

                    Z3_sort  child_sort = Z3_get_sort(ctx, child1);
                    unsigned child_sort_size =
                        Z3_get_sort_kind(ctx, child_sort) == Z3_BV_SORT
                            ? Z3_get_bv_sort_size(ctx, child_sort)
                            : 0;

                    if (child_sort_size > 64) {
                        ABORT();// res = (uint64_t)z3fuzz_evaluate_expression_z3(ctx, e);
                    } else {
                        arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                        arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                        res = arg1 == arg2 ? 1 : 0;
                    }
                    break;
                }
                case Z3_OP_NOT: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    res = arg1 ? 0 : 1;
                    break;
                }
                case Z3_OP_SGEQ: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    OPERATION(arg1, arg2, SIZE(ARG1(e)), >=, res);
                    res = res ? 1 : 0;
                    break;
                }
                case Z3_OP_SGT: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    OPERATION(arg1, arg2, SIZE(ARG1(e)), >, res);
                    res = res ? 1 : 0;
                    break;
                }
                case Z3_OP_SLEQ: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    OPERATION(arg1, arg2, SIZE(ARG1(e)), <=, res);
                    res = res ? 1 : 0;
                    break;
                }
                case Z3_OP_SLT: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    OPERATION(arg1, arg2, SIZE(ARG1(e)), <, res);
                    res = res ? 1 : 0;
                    break;
                }
                case Z3_OP_UGEQ: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = arg1 >= arg2;
                    res = res ? 1 : 0;
                    break;
                }
                case Z3_OP_UGT: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = arg1 > arg2 ? 1 : 0;
                    break;
                }
                case Z3_OP_ULEQ: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = arg1 <= arg2 ? 1 : 0;
                    break;
                }
                case Z3_OP_ULT: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = arg1 < arg2 ? 1 : 0;
                    break;
                }

                case Z3_OP_CONCAT: {
                    unsigned num_operands = Z3_get_app_num_args(ctx, app);
                    res         = 0;
                    size_t size = 0;
                    for (ssize_t i = num_operands - 1; i >= 0; --i) {
                        arg1 = conc_eval(m, n, m_others, ARG(e, i), cache,
                                         from_cache);
                        res |= (arg1 << size);
                        size += SIZE(ARG(e, i));
                    }
                    break;
                }
                case Z3_OP_EXTRACT: {
                    if (SIZE(ARG1(e)) > 64) {
                        ABORT("Size not yet supported");
                    }
                    size_t high = PARAM1(e);
                    size_t low  = PARAM2(e);
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    // printf("arg1=%lu high=%lu low=%lu mask=%lu\n", arg1,
                    // high, low, FF_MASK(high - low + 1));
                    res = (arg1 >> low) & FF_MASK(high - low + 1);
                    break;
                }
                case Z3_OP_ZERO_EXT: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
#if 0
                    size_t arg1_size = SIZE(ARG1(e));
                    size_t n_bits    = PARAM1(e);
                    arg2 = FF_MASK(n_bits) << arg1_size;
                    arg1 &= ~arg2;
#endif
                    res = arg1;
                    break;
                }
                case Z3_OP_SIGN_EXT: {
                    size_t arg1_size = SIZE(ARG1(e));
                    size_t n_bits    = PARAM1(e);
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    if (arg1 & (1 << (arg1_size - 1))) {
                        // negative number
                        arg2 = FF_MASK(n_bits) << arg1_size;
                        arg1 |= arg2;
                    }
                    res = arg1;
                    break;
                }

                case Z3_OP_AND: {
                    unsigned num_operands = Z3_get_app_num_args(ctx, app);
                    res = 1;
                    for (size_t i = 0; i < num_operands; ++i) {
                        arg1 = conc_eval(m, n, m_others, ARG(e, i), cache,
                                         from_cache);
                        if (arg1 == 0) {
                            res = 0;
                            break;
                        }
                    }
                    break;
                }
                case Z3_OP_OR: {
                    unsigned num_operands = Z3_get_app_num_args(ctx, app);
                    res = 0;
                    for (size_t i = 0; i < num_operands; ++i) {
                        arg1 = conc_eval(m, n, m_others, ARG(e, i), cache,
                                         from_cache);
                        if (arg1 == 1) {
                            res = 1;
                            break;
                        }
                    }
                    break;
                }

                case Z3_OP_BNOT: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    res = ~arg1 & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BNEG: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    res = -arg1 & FF_MASK(SIZE(e));
                    break;
                }

                case Z3_OP_BADD: {
                    unsigned num_operands = Z3_get_app_num_args(ctx, app);
                    res = 0;
                    for (size_t i = 0; i < num_operands; ++i) {
                        arg1 = conc_eval(m, n, m_others, ARG(e, i), cache,
                                         from_cache);
                        res += arg1;
                    }
                    res = res & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BSUB: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 - arg2) & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BMUL: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 * arg2) & FF_MASK(SIZE(e));
                    break;
                }

                case Z3_OP_BUDIV: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 / arg2) & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BUREM: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 % arg2) & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BSDIV_I:
                case Z3_OP_BSDIV: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    if (arg2 == 0) {
                        // compliance to Z3: division by zero yields -1
                        *from_cache = 0;
                        res = -1;
                        break;
                    }
                    OPERATION(arg1, arg2, SIZE(e), /, arg1);
                    res = arg1 & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BSREM:
                case Z3_OP_BSREM_I: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    if (arg2 == 0) {
                        // compliance to Z3: division by zero yields -1
                        *from_cache = 0;
                        res = -1;
                        break;
                    }
                    OPERATION(arg1, arg2, SIZE(e), %, arg1);
                    res = arg1 & FF_MASK(SIZE(e));
                    break;
                }

                case Z3_OP_BSHL: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 << arg2) & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BLSHR: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 >> arg2) & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BASHR: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    OPERATION(arg1, arg2, SIZE(e), >>, arg1);
                    res = arg1 & FF_MASK(SIZE(e));
                    break;
                }

                case Z3_OP_BAND: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 & arg2) & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BOR: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 | arg2) & FF_MASK(SIZE(e));
                    break;
                }
                case Z3_OP_BXOR: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                    res = (arg1 ^ arg2) & FF_MASK(SIZE(e));
                    break;
                }

                case Z3_OP_ITE: {
                    arg1 = conc_eval(m, n, m_others, ARG1(e), cache, from_cache);
                    if (arg1) {
                        arg2 = conc_eval(m, n, m_others, ARG2(e), cache, from_cache);
                        res = arg2 & FF_MASK(SIZE(e));
                    } else {
                        arg3 = conc_eval(m, n, m_others, ARG3(e), cache, from_cache);
                        res = arg3 & FF_MASK(SIZE(e));
                    }
                    break;
                }

                default: {
                    print_z3_ast(e);
                    ABORT();
                }
            }
            break;
        }

        case Z3_NUMERAL_AST: {
            uint64_t value;
            Z3_bool  r = Z3_get_numeral_uint64(ctx, e,
#if Z3_VERSION <= 451
                                              (long long unsigned int*)
#endif
                                              &value);
            assert(r == Z3_TRUE);
            res = value;
            break;
        }

        default:
            ABORT();
    }

#if 1
    if (!skip_global_cache) {
        dict_set__uint64_t(global_cache, hash, (uint64_t)res);
    }
#endif
#if 0
    printf("Inserting in cache %lx for %lu - ", res, hash);
    print_z3_ast_internal(e, 0, 0);
    printf("\n");
#endif
#if 0
    dict_set__uint64_t(cache, hash, (uint64_t)res);
#endif

    cached_value_t cache_el;
    cache_el.valid = 1;
    cache_el.value = res;
    dict_set__cached_value_t(cache, hash, cache_el);

    *from_cache = 0;
    return res;
}

static int conc_eval_uint64(uint8_t* m, size_t n, dict__uint64_t* m_others,
                            Z3_ast e, uintptr_t* value, uint8_t* from_cache)
{
    // dict__uint64_t* cache = malloc(sizeof(dict__uint64_t));
    // dict_init__uint64_t(cache);

    dict__cached_value_t cache;
    dict_init__cached_value_t(&cache);
    *value = conc_eval(m, n, m_others, e, &cache, from_cache);
    dict_free__cached_value_t(&cache, NULL);

    // dict_free__uint64_t(cache, NULL);
    // free(cache);

    if (Z3_get_ast_kind(smt_solver.ctx, e) == Z3_APP_AST) {

        Z3_sort_kind sort_kind =
            Z3_get_sort_kind(smt_solver.ctx, Z3_get_sort(smt_solver.ctx, e));
        if (sort_kind == Z3_BOOL_SORT) {
            return *value ? 1 : 0;
        } else if (sort_kind == Z3_BV_SORT) {
            return 1;
        } else {
            ABORT("Unexpected expression");
        }
    } else {
        ABORT("Unexpected expression");
    }
}

GHashTable* get_inputs_expr(Z3_ast e)
{
    if (!e) {
        return g_hash_table_new(NULL, NULL);
    }

    Z3_context ctx  = smt_solver.ctx;
    uintptr_t  hash = Z3_get_ast_id(ctx, e);
    assert(hash);

    if (!ast_to_inputs) {
        ast_to_inputs = malloc(sizeof(dict__uint64_t));
        dict_init__uint64_t(ast_to_inputs);
    }

    GHashTable* res = (GHashTable*)dict_get__uint64_t(ast_to_inputs, hash);
    if (res) {
        return res;
    }

    res = g_hash_table_new(NULL, NULL);
    dict_set__uint64_t(ast_to_inputs, hash, (uint64_t)res);

    switch (Z3_get_ast_kind(ctx, e)) {
        case Z3_NUMERAL_AST: {
            break;
        }
        case Z3_APP_AST: {

            Z3_app       app        = Z3_to_app(ctx, e);
            Z3_func_decl decl       = Z3_get_app_decl(ctx, app);
            Z3_decl_kind decl_kind  = Z3_get_decl_kind(ctx, decl);
            unsigned     num_fields = Z3_get_app_num_args(ctx, app);

            if (decl_kind == Z3_OP_UNINTERPRETED) {

                Z3_symbol   symbol = Z3_get_decl_name(ctx, decl);
                const char* s      = Z3_get_symbol_string(ctx, symbol);
                if (strncmp("in", s, 2) == 0) {
                    size_t index = strtol(s + 6, NULL, 10);
                    g_hash_table_add(res, (gpointer)index);
                } else if (strncmp("s_", s, 2) == 0 ||
                           strncmp("sv", s, 2) == 0) {
                    size_t index = hash_str(s, strlen(s));
                    g_hash_table_add(res, (gpointer)MAX_INPUT_SIZE + index);
                } else {
                    printf("Symbol: %s\n", s);
                    ABORT();
                }
            } else {
                // it is not a symbol. Recursive call
                for (size_t i = 0; i < num_fields; i++) {
                    Z3_ast child = Z3_get_app_arg(ctx, app, i);

                    GHashTable* child_inputs = get_inputs_expr(child);
                    if (child) {
                        GHashTableIter iter;
                        gpointer       key, value;
                        g_hash_table_iter_init(&iter, child_inputs);
                        while (g_hash_table_iter_next(&iter, &key, &value)) {
                            g_hash_table_add(res, key);
                        }
                    }
                }
            }

            break;
        }
    }

    return res;
}