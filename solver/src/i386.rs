use crate::expression::{Expr, OpKind};
use anyhow::Result;
use z3::ast::{self, Ast};
use z3::Context;

// x86 EFLAGS constants
const CC_C: u64 = 0x0001;
const CC_P: u64 = 0x0004;
const CC_A: u64 = 0x0010;
const CC_Z: u64 = 0x0040;
const CC_S: u64 = 0x0080;
const CC_O: u64 = 0x0800;

const SIGN_MASK: u64 = 0x8000000000000000;
const XMM_BYTES: usize = 16;

/// Helper function to create Z3 bitvector constants
fn smt_new_const(ctx: &Context, value: u64, bits: u32) -> ast::BV {
    ast::BV::from_u64(ctx, value, bits)
}

/// Helper function to perform left/right shift based on sign
fn lshift<'ctx>(ctx: &'ctx Context, x: &ast::BV<'ctx>, n: i32, width: usize) -> ast::BV<'ctx> {
    let shift_amount = ast::BV::from_u64(ctx, n.abs() as u64, (width * 8) as u32);
    if n >= 0 {
        x.bvshl(&shift_amount)
    } else {
        x.bvlshr(&shift_amount)
    }
}

/// Compute parity flag (PF) - XOR of lower 8 bits
fn eflags_pf<'ctx>(ctx: &'ctx Context, dst: &ast::BV<'ctx>, width: usize) -> ast::BV<'ctx> {
    let zero = smt_new_const(ctx, 0, (width * 8) as u32);
    let mut pf = dst.extract(0, 0);
    
    for i in 1..8 {
        let bit = dst.extract(i, i);
        pf = pf.bvxor(&bit);
    }
    
    let cond_pf = pf._eq(&smt_new_const(ctx, 0, 1));
    let cc_p = smt_new_const(ctx, CC_P, (width * 8) as u32);
    cond_pf.ite(&cc_p, &zero)
}

/// Compute overflow flag for addition-like operations
fn eflags_of_a<'ctx>(
    ctx: &'ctx Context,
    dst: &ast::BV<'ctx>,
    src1: &ast::BV<'ctx>,
    src2: &ast::BV<'ctx>,
    width: usize,
) -> ast::BV<'ctx> {
    let neg_one = smt_new_const(ctx, u64::MAX, (width * 8) as u32);
    let of_a = src1.bvxor(src2).bvxor(&neg_one);
    let of_b = src1.bvxor(dst);
    let of = of_a.bvand(&of_b);
    let shifted = lshift(ctx, &of, 12 - (8 * width as i32), width);
    let cc_o = smt_new_const(ctx, CC_O, (width * 8) as u32);
    shifted.bvand(&cc_o)
}

/// Compute overflow flag for subtraction-like operations
fn eflags_of_b<'ctx>(
    ctx: &'ctx Context,
    dst: &ast::BV<'ctx>,
    src1: &ast::BV<'ctx>,
    src2: &ast::BV<'ctx>,
    width: usize,
) -> ast::BV<'ctx> {
    let of_a = src1.bvxor(src2);
    let of_b = src1.bvxor(dst);
    let of = of_a.bvand(&of_b);
    let shifted = lshift(ctx, &of, 12 - (8 * width as i32), width);
    let cc_o = smt_new_const(ctx, CC_O, (width * 8) as u32);
    shifted.bvand(&cc_o)
}

/// EFLAGS carry flag computation for ADC operations
pub fn eflags_c_adc<'ctx>(
    ctx: &'ctx Context,
    dst: &ast::BV<'ctx>,
    src1: &ast::BV<'ctx>,
    src3_expr: &Expr,
    src3_is_const: bool,
    width: usize,
) -> Result<ast::BV<'ctx>> {
    let mask = (1u64 << (width * 8)) - 1;
    
    if src3_is_const {
        let src3_val = src3_expr as *const Expr as usize as u64;
        let cond_result = if (src3_val & mask) != 0 {
            dst.bvule(src1)
        } else {
            dst.bvult(src1)
        };
        // Convert Bool to BV
        let one = smt_new_const(ctx, 1, (width * 8) as u32);
        let zero = smt_new_const(ctx, 0, (width * 8) as u32);
        Ok(cond_result.ite(&one, &zero))
    } else {
        // For symbolic src3, we need to handle both cases
        let zero = smt_new_const(ctx, 0, (width * 8) as u32);
        let one = smt_new_const(ctx, 1, (width * 8) as u32);
        // Convert src3 expression to BV - simplified implementation
        let src3 = smt_new_const(ctx, 0, (width * 8) as u32); // Placeholder: would convert src3_expr in full implementation
        let cond = src3._eq(&zero).not();
        let a = dst.bvule(src1).ite(&one, &zero);
        let b = dst.bvult(src1).ite(&one, &zero);
        Ok(cond.ite(&a, &b))
    }
}

/// EFLAGS carry flag computation for SBB operations
pub fn eflags_c_sbb<'ctx>(
    ctx: &'ctx Context,
    dst: &ast::BV<'ctx>,
    src2: &ast::BV<'ctx>,
    src3: &ast::BV<'ctx>,
    width: usize,
) -> ast::BV<'ctx> {
    let src1 = dst.bvadd(src2).bvadd(src3);
    let zero = smt_new_const(ctx, 0, (width * 8) as u32);
    let one = smt_new_const(ctx, 1, (width * 8) as u32);
    let cond = src3._eq(&zero).not();
    let a = src1.bvule(src2).ite(&one, &zero);
    let b = src1.bvult(src2).ite(&one, &zero);
    cond.ite(&a, &b)
}

/// EFLAGS carry flag computation for binary operations
pub fn eflags_c_binary<'ctx>(
    ctx: &'ctx Context,
    dst: &ast::BV<'ctx>,
    src1: &ast::BV<'ctx>,
    opkind: OpKind,
    width: usize,
) -> Result<ast::BV<'ctx>> {
    let zero = smt_new_const(ctx, 0, (width * 8) as u32);
    let one = smt_new_const(ctx, 1, (width * 8) as u32);
    
    match opkind {
        OpKind::EflagsCAdd => {
            // dst < src1
            Ok(dst.bvult(src1).ite(&one, &zero))
        }
        OpKind::EflagsCSub => {
            // args are swapped: src1 = dst + src2, then src1 < src2
            let src2 = src1;
            let new_src1 = dst.bvadd(src2);
            Ok(new_src1.bvult(src2).ite(&one, &zero))
        }
        OpKind::EflagsCShl => {
            // (src1 >> (DATA_BITS - 1)) & CC_C
            let shift_amt = smt_new_const(ctx, ((8 * width) - 1) as u64, (8 * width) as u32);
            let shifted = src1.bvashr(&shift_amt);
            let cc_c = smt_new_const(ctx, CC_C, (8 * width) as u32);
            Ok(shifted.bvand(&cc_c))
        }
        OpKind::EflagsCBmilg => {
            // src1 == 0
            let cond = src1._eq(&zero);
            Ok(cond.ite(&one, &zero))
        }
        _ => anyhow::bail!("Unknown EFLAGS_C binary opkind: {:?}", opkind),
    }
}

/// Complete EFLAGS computation for binary operations
pub fn eflags_all_binary<'ctx>(
    ctx: &'ctx Context,
    dst: &ast::BV<'ctx>,
    src1: &ast::BV<'ctx>,
    opkind: OpKind,
    width: usize,
) -> Result<ast::BV<'ctx>> {
    let zero = smt_new_const(ctx, 0, (width * 8) as u32);
    let one = smt_new_const(ctx, 1, (width * 8) as u32);

    let (cf, pf, af, zf, sf, of) = match opkind {
        OpKind::EflagsAllAdd => {
            let src2 = dst.bvsub(src1);
            let cf = dst.bvult(src1).ite(&one, &zero);
            let pf = eflags_pf(ctx, dst, width);
            let af = dst.bvxor(src1).bvxor(&src2).bvand(&smt_new_const(ctx, CC_A, (width * 8) as u32));
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let of = eflags_of_a(ctx, dst, src1, &src2, width);
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllSub => {
            let src2 = src1;
            let new_src1 = dst.bvadd(src2);
            let cf = new_src1.bvult(src2).ite(&one, &zero);
            let pf = eflags_pf(ctx, dst, width);
            let af = dst.bvxor(&new_src1).bvxor(src2).bvand(&smt_new_const(ctx, CC_A, (width * 8) as u32));
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let of = eflags_of_b(ctx, dst, &new_src1, src2, width);
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllLogic => {
            let cf = zero.clone();
            let pf = eflags_pf(ctx, dst, width);
            let af = zero.clone();
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let of = zero.clone();
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllInc => {
            let cf = src1.clone();
            let new_src1 = dst.bvsub(&one);
            let src2 = one.clone();
            let pf = eflags_pf(ctx, dst, width);
            let af = dst.bvxor(&new_src1).bvxor(&src2).bvand(&smt_new_const(ctx, CC_A, (width * 8) as u32));
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let sign_mask = smt_new_const(ctx, SIGN_MASK - 1, (width * 8) as u32);
            let of_cond = dst._eq(&sign_mask);
            let of = of_cond.ite(&smt_new_const(ctx, CC_O, (width * 8) as u32), &zero);
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllDec => {
            let cf = src1.clone();
            let new_src1 = dst.bvadd(&one);
            let src2 = one.clone();
            let pf = eflags_pf(ctx, dst, width);
            let af = dst.bvxor(&new_src1).bvxor(&src2).bvand(&smt_new_const(ctx, CC_A, (width * 8) as u32));
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let sign_mask = smt_new_const(ctx, SIGN_MASK - 1, (width * 8) as u32);
            let of_cond = dst._eq(&sign_mask);
            let of = of_cond.ite(&smt_new_const(ctx, CC_O, (width * 8) as u32), &zero);
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllShl => {
            let w = smt_new_const(ctx, ((8 * width) - 1) as u64, (8 * width) as u32);
            let cf = src1.bvlshr(&w).bvand(&smt_new_const(ctx, CC_C, (width * 8) as u32));
            let pf = eflags_pf(ctx, dst, width);
            let af = zero.clone();
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let of = src1.bvxor(dst);
            let of = lshift(ctx, &of, 12 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_O, (width * 8) as u32));
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllSar => {
            let cf = src1.bvand(&one);
            let pf = eflags_pf(ctx, dst, width);
            let af = zero.clone();
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let of = src1.bvxor(dst);
            let of = lshift(ctx, &of, 12 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_O, (width * 8) as u32));
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllMul => {
            let zero64 = smt_new_const(ctx, 0, 64);
            let cf_cond = src1._eq(&zero64).not();
            let cf = cf_cond.ite(&one, &zero);
            let pf = eflags_pf(ctx, dst, width);
            let af = zero.clone();
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let of = cf_cond.ite(&smt_new_const(ctx, CC_O, (width * 8) as u32), &zero);
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllBmilg => {
            let cf_cond = src1._eq(&zero);
            let cf = cf_cond.ite(&one, &zero);
            let pf = zero.clone();
            let af = zero.clone();
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, CC_Z, (width * 8) as u32), &zero);
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, CC_S, (width * 8) as u32));
            let of = zero.clone();
            (cf, pf, af, zf, sf, of)
        }
        _ => anyhow::bail!("Unknown EFLAGS_ALL binary opkind: {:?}", opkind),
    };

    // Combine all flags with OR
    let result = cf.bvor(&pf).bvor(&af).bvor(&zf).bvor(&sf).bvor(&of);
    Ok(result)
}

/// Complete EFLAGS computation for ternary operations (ADC/SBB variants)
pub fn eflags_all_ternary<'ctx>(
    ctx: &'ctx Context,
    dst: &ast::BV<'ctx>,
    src1: &ast::BV<'ctx>,
    src3: &ast::BV<'ctx>,
    opkind: OpKind,
    width: usize,
) -> Result<ast::BV<'ctx>> {
    let zero = smt_new_const(ctx, 0, (width * 8) as u32);

    let (cf, pf, af, zf, sf, of) = match opkind {
        OpKind::EflagsAllAdcb | OpKind::EflagsAllAdcw | OpKind::EflagsAllAdcl | OpKind::EflagsAllAdcq => {
            let src2 = dst.bvsub(src1).bvsub(src3);
            let one = smt_new_const(ctx, 1, (width * 8) as u32);
            let cf_cond = src3._eq(&zero).not();
            let cf_a = dst.bvule(src1).ite(&one, &zero);
            let cf_b = dst.bvult(src1).ite(&one, &zero);
            let cf = cf_cond.ite(&cf_a, &cf_b);
            let pf = eflags_pf(ctx, dst, width);
            let af = dst.bvxor(src1).bvxor(&src2).bvand(&smt_new_const(ctx, 0x10, (width * 8) as u32));
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, 1, (width * 8) as u32), &zero);
            let zf = zf.bvshl(&smt_new_const(ctx, 6, (width * 8) as u32));
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, 0x80, (width * 8) as u32));
            let of = eflags_of_a(ctx, dst, src1, &src2, width);
            (cf, pf, af, zf, sf, of)
        }
        OpKind::EflagsAllSbbb | OpKind::EflagsAllSbbw | OpKind::EflagsAllSbbl | OpKind::EflagsAllSbbq => {
            let src2 = src1;
            let new_src1 = dst.bvadd(src2).bvadd(src3);
            let one = smt_new_const(ctx, 1, (width * 8) as u32);
            let cf_cond = src3._eq(&zero).not();
            let cf_a = new_src1.bvule(src2).ite(&one, &zero);
            let cf_b = new_src1.bvult(src2).ite(&one, &zero);
            let cf = cf_cond.ite(&cf_a, &cf_b);
            let pf = eflags_pf(ctx, dst, width);
            let af = dst.bvxor(&new_src1).bvxor(src2).bvand(&smt_new_const(ctx, 0x10, (width * 8) as u32));
            let zf_cond = dst._eq(&zero);
            let zf = zf_cond.ite(&smt_new_const(ctx, 1, (width * 8) as u32), &zero);
            let zf = zf.bvshl(&smt_new_const(ctx, 6, (width * 8) as u32));
            let sf = lshift(ctx, dst, 8 - (8 * width as i32), width).bvand(&smt_new_const(ctx, 0x80, (width * 8) as u32));
            let of = eflags_of_b(ctx, dst, &new_src1, src2, width);
            (cf, pf, af, zf, sf, of)
        }
        _ => anyhow::bail!("Unknown EFLAGS_ALL ternary opkind: {:?}", opkind),
    };

    // Combine all flags with OR
    let result = cf.bvor(&pf).bvor(&af).bvor(&zf).bvor(&sf).bvor(&of);
    Ok(result)
}

/// EFLAGS computation for ADCX/ADOX operations
pub fn eflags_all_adcxo<'ctx>(
    ctx: &'ctx Context,
    dst: &ast::BV<'ctx>,
    src1: &ast::BV<'ctx>,
    src2: &ast::BV<'ctx>,
    opkind: OpKind,
) -> Result<ast::BV<'ctx>> {
    let zero = smt_new_const(ctx, 0, 64);

    match opkind {
        OpKind::EflagsAllAdcx => {
            // (src1 & ~CC_C) | (dst * CC_C)
            let r0 = src1.bvand(&smt_new_const(ctx, !CC_C, 64));
            let r1_cond = dst._eq(&zero);
            let r1 = r1_cond.ite(&zero, &smt_new_const(ctx, CC_C, 64));
            Ok(r0.bvor(&r1))
        }
        OpKind::EflagsAllAdox => {
            // (src1 & ~CC_O) | (src2 * CC_O)
            let r0 = src1.bvand(&smt_new_const(ctx, !CC_O, 64));
            let r1_cond = src2._eq(&zero);
            let r1 = r1_cond.ite(&zero, &smt_new_const(ctx, CC_O, 64));
            Ok(r0.bvor(&r1))
        }
        OpKind::EflagsAllAdcox => {
            // (src1 & ~(CC_C | CC_O)) | (dst * CC_C) | (src2 * CC_O)
            let r0 = src1.bvand(&smt_new_const(ctx, !(CC_C | CC_O), 64));
            let r1_cond = dst._eq(&zero);
            let r1 = r1_cond.ite(&zero, &smt_new_const(ctx, CC_C, 64));
            let r2_cond = src2._eq(&zero);
            let r2 = r2_cond.ite(&zero, &smt_new_const(ctx, CC_O, 64));
            Ok(r0.bvor(&r1).bvor(&r2))
        }
        _ => anyhow::bail!("Unknown EFLAGS_ALL ADCXO opkind: {:?}", opkind),
    }
}

/// Handle comparison operations
pub fn handle_comparison<'ctx>(
    ctx: &'ctx Context,
    op1: &ast::BV<'ctx>,
    op2: &ast::BV<'ctx>,
    opkind: OpKind,
    width: usize,
) -> Result<ast::BV<'ctx>> {
    let cmp_result = match opkind {
        OpKind::CmpEq => op1._eq(op2),
        OpKind::CmpGt => op1.bvsgt(op2),
        OpKind::CmpGe => op1.bvsge(op2),
        OpKind::CmpLt => op1.bvslt(op2),
        OpKind::CmpLe => op1.bvsle(op2),
        _ => anyhow::bail!("Unknown comparison opkind: {:?}", opkind),
    };

    let ones = smt_new_const(ctx, (1u64 << (width * 8)) - 1, (width * 8) as u32);
    let zeros = smt_new_const(ctx, 0, (width * 8) as u32);
    Ok(cmp_result.ite(&ones, &zeros))
}

/// Handle MIN/MAX operations
pub fn handle_min_max<'ctx>(
    _ctx: &'ctx Context,
    op1: &ast::BV<'ctx>,
    op2: &ast::BV<'ctx>,
    opkind: OpKind,
) -> Result<ast::BV<'ctx>> {
    match opkind {
        OpKind::Min => {
            let cond = op1.bvule(op2);
            Ok(cond.ite(op1, op2))
        }
        OpKind::Max => {
            let cond = op1.bvuge(op2);
            Ok(cond.ite(op1, op2))
        }
        _ => anyhow::bail!("Unknown MIN/MAX opkind: {:?}", opkind),
    }
}

/// Handle PMOVMSKB operation (pack mask to byte)
pub fn handle_pmovmskb<'ctx>(
    ctx: &'ctx Context,
    op1: &ast::BV<'ctx>,
) -> Result<ast::BV<'ctx>> {
    let mut result = op1.extract(7, 7); // MSB of first byte
    
    for i in 1..XMM_BYTES {
        let msb = (8 * (i + 1)) - 1;
        let bit = op1.extract(msb as u32, msb as u32);
        result = bit.concat(&result);
    }
    
    let zeros = smt_new_const(ctx, 0, 64 - XMM_BYTES as u32);
    Ok(zeros.concat(&result))
}

/// Helper function to translate operands to Z3 bitvectors
fn translate_operand<'ctx>(
    ctx: &'ctx Context,
    operand: *mut Expr,
    is_const: bool,
    width: usize,
) -> Result<ast::BV<'ctx>> {
    if is_const {
        let value = operand as usize as u64;
        Ok(smt_new_const(ctx, value, (width * 8) as u32))
    } else {
        // For symbolic operands, create a symbolic bitvector
        // In a full implementation, this would recursively translate the expression
        let symbol_name = format!("sym_{:p}", operand);
        Ok(ast::BV::new_const(ctx, symbol_name, (width * 8) as u32))
    }
}

/// Get operation width from opkind
fn get_opkind_width(opkind: OpKind) -> usize {
    match opkind {
        OpKind::EflagsAllAdcb | OpKind::EflagsAllSbbb | OpKind::EflagsCAdcb | OpKind::EflagsCSbbb => 1,
        OpKind::EflagsAllAdcw | OpKind::EflagsAllSbbw | OpKind::EflagsCAdcw | OpKind::EflagsCSbbw => 2,
        OpKind::EflagsAllAdcl | OpKind::EflagsAllSbbl | OpKind::EflagsCAdcl | OpKind::EflagsCSbbl => 4,
        OpKind::EflagsAllAdcq | OpKind::EflagsAllSbbq | OpKind::EflagsCAdcq | OpKind::EflagsCSbbq => 8,
        _ => 8, // Default to 8 bytes for other operations
    }
}

/// Main i386 query translation function - converts i386-specific expressions to Z3 AST
pub fn smt_query_i386_to_z3<'ctx>(
    ctx: &'ctx Context,
    query: &Expr,
    width: usize,
) -> Result<ast::Dynamic<'ctx>> {
    use crate::expression::OpKind;
    
    // Convert u8 opkind to OpKind enum for pattern matching
    let opkind = unsafe { std::mem::transmute::<u8, OpKind>(query.opkind) };
    
    match opkind {
        // Comparison operations
        OpKind::CmpEq | OpKind::CmpGt | OpKind::CmpGe | OpKind::CmpLt | OpKind::CmpLe => {
            let slice = unsafe { query.op3 as *const Expr as usize };
            let slice = if slice <= 8 { slice } else { width };
            
            let op1 = translate_operand(ctx, query.op1, query.op1_is_const != 0, slice)?;
            let op2 = translate_operand(ctx, query.op2, query.op2_is_const != 0, slice)?;
            
            let result = handle_comparison(ctx, &op1, &op2, opkind, slice)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        // PMOVMSKB operation
        OpKind::Pmovmskb => {
            let op1 = translate_operand(ctx, query.op1, query.op1_is_const != 0, 16)?; // XMM register is 16 bytes
            let result = handle_pmovmskb(ctx, &op1)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        // MIN/MAX operations
        OpKind::Min | OpKind::Max => {
            let slice = unsafe { query.op3 as *const Expr as usize };
            let slice = if slice <= 8 { slice } else { width };
            
            let op1 = translate_operand(ctx, query.op1, query.op1_is_const != 0, slice)?;
            let op2 = translate_operand(ctx, query.op2, query.op2_is_const != 0, slice)?;
            
            let result = handle_min_max(ctx, &op1, &op2, opkind)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        // EFLAGS binary operations (ADD, SUB, MUL, LOGIC, INC, DEC, SHL, SAR, BMILG)
        OpKind::EflagsAllAdd | OpKind::EflagsAllSub | OpKind::EflagsAllMul | 
        OpKind::EflagsAllLogic | OpKind::EflagsAllInc | OpKind::EflagsAllDec |
        OpKind::EflagsAllShl | OpKind::EflagsAllSar | OpKind::EflagsAllBmilg => {
            let op_width = get_opkind_width(opkind);
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, op_width)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, op_width)?;
            
            let result = eflags_all_binary(ctx, &dst, &src1, opkind, op_width)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        // EFLAGS ternary operations (ADC, SBB)
        OpKind::EflagsAllAdcb | OpKind::EflagsAllAdcw | OpKind::EflagsAllAdcl | OpKind::EflagsAllAdcq |
        OpKind::EflagsAllSbbb | OpKind::EflagsAllSbbw | OpKind::EflagsAllSbbl | OpKind::EflagsAllSbbq => {
            let op_width = get_opkind_width(opkind);
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, op_width)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, op_width)?;
            let carry = translate_operand(ctx, query.op3, false, 1)?; // Carry is always 1 bit
            
            let result = eflags_all_ternary(ctx, &dst, &src1, &carry, opkind, op_width)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        // EFLAGS ADCX/ADOX operations
        OpKind::EflagsAllAdcx | OpKind::EflagsAllAdox | OpKind::EflagsAllAdcox => {
            let op_width = get_opkind_width(opkind);
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, op_width)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, op_width)?;
            let carry = translate_operand(ctx, query.op3, false, 1)?;
            
            let result = eflags_all_adcxo(ctx, &dst, &src1, &carry, opkind)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        // EFLAGS carry-only operations
        OpKind::EflagsCAdd | OpKind::EflagsCSub | OpKind::EflagsCMul | 
        OpKind::EflagsCLogic | OpKind::EflagsCShl => {
            let op_width = get_opkind_width(opkind);
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, op_width)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, op_width)?;
            
            let result = eflags_c_binary(ctx, &dst, &src1, opkind, op_width)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        // EFLAGS carry-only ADC operations
        OpKind::EflagsCAdcb => {
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, 1)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, 1)?;
            let result = eflags_c_adc(ctx, &dst, &src1, unsafe { &*query.op3 }, false, 1)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        OpKind::EflagsCAdcw => {
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, 2)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, 2)?;
            let result = eflags_c_adc(ctx, &dst, &src1, unsafe { &*query.op3 }, false, 2)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        OpKind::EflagsCAdcl => {
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, 4)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, 4)?;
            let result = eflags_c_adc(ctx, &dst, &src1, unsafe { &*query.op3 }, false, 4)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        OpKind::EflagsCAdcq => {
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, 8)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, 8)?;
            let result = eflags_c_adc(ctx, &dst, &src1, unsafe { &*query.op3 }, false, 8)?;
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        // EFLAGS carry-only SBB operations
        OpKind::EflagsCSbbb => {
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, 1)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, 1)?;
            let carry = translate_operand(ctx, query.op3, false, 1)?;
            let result = eflags_c_sbb(ctx, &dst, &src1, &carry, 1);
            Ok(ast::Dynamic::from_ast(&result))
        }
        OpKind::EflagsCSbbw => {
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, 2)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, 2)?;
            let carry = translate_operand(ctx, query.op3, false, 1)?;
            let result = eflags_c_sbb(ctx, &dst, &src1, &carry, 2);
            Ok(ast::Dynamic::from_ast(&result))
        }
        OpKind::EflagsCSbbl => {
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, 4)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, 4)?;
            let carry = translate_operand(ctx, query.op3, false, 1)?;
            let result = eflags_c_sbb(ctx, &dst, &src1, &carry, 4);
            Ok(ast::Dynamic::from_ast(&result))
        }
        OpKind::EflagsCSbbq => {
            let dst = translate_operand(ctx, query.op1, query.op1_is_const != 0, 8)?;
            let src1 = translate_operand(ctx, query.op2, query.op2_is_const != 0, 8)?;
            let carry = translate_operand(ctx, query.op3, false, 1)?;
            let result = eflags_c_sbb(ctx, &dst, &src1, &carry, 8);
            Ok(ast::Dynamic::from_ast(&result))
        }
        
        _ => {
            anyhow::bail!("Unsupported i386 opkind: {:?}", query.opkind);
        }
    }
}
