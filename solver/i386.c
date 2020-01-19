#include "solver.h"
#include "i386.h"

#define VERBOSE 0
static inline Z3_ast eflags_c_adc(Z3_context ctx, Expr* query, size_t width)
{
    // from TCG cc_helper.c
    // src3 ? dst <= src1 : dst < src1;

    Z3_ast dst = smt_query_to_z3(query->op1, query->op1_is_const, width);
    Z3_ast src1 = smt_query_to_z3(query->op2, query->op2_is_const, width);

    if (width < sizeof(uintptr_t)) {
        dst = smt_bv_extract(dst, width);
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
        smt_print_ast_sort(cond);
        Z3_ast a    = Z3_mk_bvule(ctx, dst, src1);
        Z3_ast b    = Z3_mk_bvult(ctx, dst, src1);
        r           = Z3_mk_ite(ctx, cond, a, b);
#if VERBOSE
        printf("EFLAGS_C_ADCQ: symbolic src3 done\n");
#endif
    }

    return r;
}

static inline Z3_ast eflags_all_adc(Z3_context ctx, Expr* query, size_t width)
{
#if 0
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

    return NULL;

#if 0
    size_t width = get_op_width(cc_op);

    Expr* src2   = new_expr();
    src2->opkind = SUB;

    if (s_temps[dst_idx]) {
        src2->op1 = s_temps[dst_idx];
    } else {
        src2->op1          = (Expr*)dst;
        src2->op1_is_const = 1;
    }

    if (s_temps[src1_idx]) {
        src2->op2 = s_temps[src1_idx];
    } else {
        src2->op2          = (Expr*)src1;
        src2->op2_is_const = 1;
    }

    Expr* cf         = new_expr();
    cf->opkind       = LTU;
    cf->op1          = src2->op1;
    cf->op1_is_const = src2->op1_is_const;
    cf->op2          = src2->op2;
    cf->op2_is_const = src2->op2_is_const;

    Expr* pf = new_expr();

    Expr* af_partial         = new_expr();
    af_partial->opkind       = XOR_3;
    af_partial->op1          = src2->op1;
    af_partial->op1_is_const = src2->op1_is_const;
    af_partial->op2          = src2->op2;
    af_partial->op2_is_const = src2->op2_is_const;
    af_partial->op3          = src2;
    Expr* af                 = new_expr();
    af->opkind               = AND;
    af->op1                  = af_partial;
    af->op2                  = (Expr*)CC_A;
    af->op2_is_const         = 1;

    Expr* zf         = new_expr();
    zf->opkind       = ITE_EQ_ZERO;
    zf->op1          = src2->op1;
    zf->op1_is_const = src2->op1_is_const;
    zf->op2          = (Expr*)CC_Z;
    zf->op2_is_const = 1;

    int   shift_count        = 8 - (width * 8);
    Expr* sf_partial         = new_expr();
    sf_partial->opkind       = shift_count >= 0 ? SAL : SAR;
    sf_partial->op1          = src2->op1;
    sf_partial->op1_is_const = src2->op1_is_const;
    sf_partial->op2          = (Expr*)(uintptr_t)shift_count;
    sf_partial->op2_is_const = 1;
    Expr* sf                 = new_expr();
    sf->opkind               = AND;
    sf->op1                  = sf_partial;
    sf->op2                  = (Expr*)(uintptr_t)CC_S;
    sf->op2_is_const         = 1;

    // of = lshift((src1 ^ src2 ^ -1) & (src1 ^ dst), 12 - DATA_BITS) & CC_O;
    Expr* of_partial_1 = new_expr();
    
    Expr* of_partial_2 = new_expr();
    Expr* of = new_expr();

    Expr* eflags_0 = new_expr();
    Expr* eflags_1 = new_expr();
    Expr* eflags_2 = new_expr();

    eflags_0->opkind = OR_3;
    eflags_0->op1    = cf;
    eflags_0->op2    = pf;
    eflags_0->op3    = eflags_1;

    eflags_1->opkind = OR_3;
    eflags_1->op1    = af;
    eflags_1->op2    = zf;
    eflags_1->op3    = eflags_1;

    eflags_2->opkind = OR;
    eflags_2->op1    = sf;
    eflags_2->op2    = of;

    s_temps[ret_idx] = eflags_0;
#endif
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
#if 0
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
#endif
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
