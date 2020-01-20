#include "solver.h"
#include "i386.h"

#define VERBOSE 0
static inline Z3_ast eflags_c_adc(Z3_context ctx, Expr* query, size_t width)
{
    // from TCG cc_helper.c
    // src3 ? dst <= src1 : dst < src1;
    // src3, dst, and src1 must be evaluated based on operation size

    Z3_ast dst  = smt_query_to_z3(query->op1, query->op1_is_const, width);
    Z3_ast src1 = smt_query_to_z3(query->op2, query->op2_is_const, width);

    if (width < sizeof(uintptr_t)) {
        dst  = smt_bv_extract(dst, width);
        src1 = smt_bv_extract(src1, width);
    }

    Expr*   src3_expr     = query->op3;
    uint8_t src3_is_const = query->op3_is_const;

#if VERBOSE
    printf("EFLAGS_C_ADCQ\n");
    smt_print_ast_sort(dst);
    smt_print_ast_sort(src1);
#endif

    Z3_ast r;
    if (src3_is_const) {
        // one of the two must be symbolic
        assert(!query->op1_is_const && !query->op2_is_const);
        uintptr_t mask = (1 << (width * 8)) - 1;
        if (((uintptr_t)src3_expr) & mask) {
            r = Z3_mk_bvule(ctx, dst, src1);
        } else {
            r = Z3_mk_bvult(ctx, dst, src1);
        }
    } else {
        // ToDo: concretize a and b when both are concrete
#if VERBOSE
        printf("EFLAGS_C_ADCQ: symbolic src3\n");
        print_expr(query->op3);
#endif
        Z3_ast src3 = smt_query_to_z3(query->op3, query->op3_is_const, width);
        // src3 is a boolean, no need to cast it
#if VERBOSE
        smt_print_ast_sort(src3);
#endif
        Z3_ast zero = smt_new_const(0, 64);
        Z3_ast cond = Z3_mk_not(ctx, Z3_mk_eq(ctx, smt_to_bv(src3), zero));
        Z3_ast a    = Z3_mk_bvule(ctx, dst, src1);
        Z3_ast b    = Z3_mk_bvult(ctx, dst, src1);
        r           = Z3_mk_ite(ctx, cond, a, b);
#if VERBOSE
        printf("EFLAGS_C_ADCQ: symbolic src3 done\n");
#endif
    }

    return r;
}
#undef VERBOSE

static inline Z3_ast lshift(Z3_context ctx, Z3_ast x, int n, size_t width)
{
    if (n >= 0) {
        return Z3_mk_bvshl(ctx, x, smt_new_const(n, width * 8));
    } else {
        return Z3_mk_bvlshr(ctx, x, smt_new_const(-n, width * 8));
    }
}

#define VERBOSE 0
static inline Z3_ast eflags_all_add(Z3_context ctx, Expr* query, size_t width)
{
#if 0
    // from TCG cc_helper.c
    int cf, pf, af, zf, sf, of;
    DATA_TYPE src2 = dst - src1;

    cf = dst < src1;
    pf = parity_table[(uint8_t)dst];
    af = (dst ^ src1 ^ src2) & CC_A;
    zf = (dst == 0) * CC_Z;
    sf = lshift(dst, 8 - DATA_BITS) & CC_S;
    of = lshift((src1 ^ src2 ^ -1) & (src1 ^ dst), 12 - DATA_BITS) & CC_O;
    return cf | pf | af | zf | sf | of;
#endif

    Z3_ast cf, pf, af, zf, sf, of;

    Z3_ast dst  = smt_query_to_z3(query->op1, query->op1_is_const, width);
    Z3_ast src1 = smt_query_to_z3(query->op2, query->op2_is_const, width);

    if (width < sizeof(uintptr_t)) {
        dst  = smt_bv_extract(dst, width);
        src1 = smt_bv_extract(src1, width);
    }

    Z3_ast src2 = Z3_mk_bvsub(ctx, dst, src1);
    Z3_ast zero = smt_new_const(0, width * 8);

#if VERBOSE
    printf("EFLAGS_ALL_ADC\n");
    smt_print_ast_sort(dst);
    smt_print_ast_sort(src1);
#endif

    cf = Z3_mk_bvult(ctx, dst, src1);
    cf = smt_to_bv(cf);
#if VERBOSE
    smt_print_ast_sort(cf);
#endif

    size_t i;
    for (i = 0; i < 8; i++) { // PF is computed only on the LSB
        Z3_ast bit = Z3_mk_extract(ctx, i, i, dst);
        if (i == 0) {
            pf = bit;
        } else {
            pf = Z3_mk_bvxor(ctx, pf, bit);
        }
    }
    Z3_ast cond_pf = Z3_mk_eq(ctx, pf, smt_new_const(0, 1));
    pf = Z3_mk_ite(ctx, cond_pf, zero, smt_new_const(CC_P, width * 8));
#if VERBOSE
    smt_print_ast_sort(pf);
#endif

    af = Z3_mk_bvxor(ctx, dst, src1);
    af = Z3_mk_bvxor(ctx, af, src2);
    af = Z3_mk_bvand(ctx, af, smt_new_const(CC_A, width * 8));
#if VERBOSE
    smt_print_ast_sort(af);
#endif

    Z3_ast cond_zf = Z3_mk_eq(ctx, dst, zero);
    zf = Z3_mk_ite(ctx, cond_zf, smt_new_const(CC_Z, width * 8), zero);
#if VERBOSE
    smt_print_ast_sort(zf);
#endif

    sf = lshift(ctx, dst, 8 - (8 * width), width);
    sf = Z3_mk_bvand(ctx, sf, smt_new_const(CC_S, width * 8));
#if VERBOSE
    smt_print_ast_sort(sf);
#endif

    Z3_ast of_a = Z3_mk_bvxor(ctx, src1, src2);
    of_a        = Z3_mk_bvxor(ctx, of_a, smt_new_const(-1, width * 8));
    Z3_ast of_b = Z3_mk_bvxor(ctx, src1, dst);
    of          = Z3_mk_bvand(ctx, of_a, of_b);
    of          = lshift(ctx, dst, 12 - (8 * width), width);
    of          = Z3_mk_bvand(ctx, of, smt_new_const(CC_O, width * 8));
#if VERBOSE
    smt_print_ast_sort(of);
#endif

    Z3_ast r = Z3_mk_bvor(ctx, cf, pf);
    r        = Z3_mk_bvor(ctx, r, af);
    r        = Z3_mk_bvor(ctx, r, zf);
    r        = Z3_mk_bvor(ctx, r, sf);
    r        = Z3_mk_bvor(ctx, r, of);

    return r;
}

Z3_ast smt_query_i386_to_z3(Z3_context ctx, Expr* query, uintptr_t is_const,
                            size_t width)
{
    assert(!is_const && "is_const is true in a i386 query");

    Z3_ast op1 = NULL;
    Z3_ast op2 = NULL;
    Z3_ast r   = NULL;
    switch (query->opkind) {

            // case RCL:

        case CMPB:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 1);
            op2 = smt_query_to_z3(query->op2, query->op2_is_const, 1);
            // printf("CMPB\n");
            // smt_print_ast_sort(op1);
            // smt_print_ast_sort(op2);
            r            = Z3_mk_eq(ctx, op1, op2);
            Z3_ast ones  = smt_new_const(0xFF, 8);
            Z3_ast zeros = smt_new_const(0, 8);
            r            = Z3_mk_ite(ctx, r, ones, zeros);
            break;
        case PMOVMSKB:
            op1 = smt_query_to_z3(query->op1, query->op1_is_const, 0);
            // printf("PMOVMSKB\n");
            for (size_t i = 0; i < XMM_BITES; i++) {
                unsigned msb = (8 * (i + 1)) - 1;
                Z3_ast   bit = Z3_mk_extract(ctx, msb, msb, op1);
                if (i == 0) {
                    r = bit;
                } else {
                    r = Z3_mk_concat(ctx, bit, r);
                }
                // smt_print_ast_sort(r);
            }
            zeros = smt_new_const(0, 64 - XMM_BITES);
            r     = Z3_mk_concat(ctx, zeros, r);
            // smt_print_ast_sort(r);
            break;
        case EFLAGS_ALL_ADD:
            r = eflags_all_add(ctx, query, (uintptr_t)query->op3);
            break;
#if 0
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
#endif
        case EFLAGS_C_ADCB:
            r = eflags_c_adc(ctx, query, 1);
            break;
        case EFLAGS_C_ADCW:
            r = eflags_c_adc(ctx, query, 2);
            break;
        case EFLAGS_C_ADCL:
            r = eflags_c_adc(ctx, query, 4);
            break;
        case EFLAGS_C_ADCQ:
            r = eflags_c_adc(ctx, query, 8);
            break;
#if 0
        case EFLAGS_C_SUB:
        case EFLAGS_C_MUL:
        case EFLAGS_C_SBBB:
        case EFLAGS_C_SBBW:
        case EFLAGS_C_SBBL:
        case EFLAGS_C_SBBQ:
        case EFLAGS_C_LOGIC:
        case EFLAGS_C_SHL:
#endif

        default:
            ABORT("Unknown expr i386 opkind: %u", query->opkind);
    }

    return r;
}
