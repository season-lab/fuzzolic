use anyhow::Result;
use z3::ast::Ast;
use crate::expressions::expression::{Expr, OpKind};
use crate::solver::SMTSolver;
use crate::solver::i386;

impl SMTSolver {
    /// Helper: translate an operand that can be either a constant (embedded in the pointer)
    /// or a pointer to another Expr node. Mirrors the C-side encoding using op*_is_const flags.
    fn translate_operand_static<'a>(ctx: &'a z3::Context, operand: *mut Expr, is_const: u8) -> Result<z3::ast::Dynamic<'a>> {
        if is_const != 0 {
            let value = operand as u64;
            // Default to 64-bit BV for constants. Callers can reinterpret as needed.
            Ok(z3::ast::BV::from_u64(ctx, value, 64).into())
        } else {
            if operand.is_null() {
                anyhow::bail!("Null (non-const) operand encountered in translation")
            }
            // SAFETY: operand points to a valid Expr node provided by QEMU side
            Self::translate_expression_static(ctx, unsafe { &*operand })
        }
    }

    /// Static expression translation method for avoiding borrowing conflicts
    pub fn translate_expression_static<'a>(ctx: &'a z3::Context, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        let op = OpKind::try_from(expr.opkind)?;
        match op {
            OpKind::Not => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                if let Some(b) = v.as_bool() { Ok(b.not().into()) } else { Ok(v.as_bv().ok_or_else(|| anyhow::anyhow!("Not op1 not BV/bool"))?.bvnot().into()) }
            }
            OpKind::Neg => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                Ok(v.as_bv().ok_or_else(|| anyhow::anyhow!("Neg op1 not BV"))?.bvneg().into())
            }
            OpKind::IsConst => {
                let value = expr.op1 as u64;
                Ok(z3::ast::BV::from_u64(ctx, value, 64).into())
            }
            // Create a BV symbol for input bytes: input_{id}
            OpKind::IsSymbolic => {
                let input_id = expr.op1 as u64;
                // Default to 8-bit symbols (byte-level) unless size is provided as const in op2
                let n_bits: u32 = if expr.op2_is_const != 0 { (expr.op2 as usize as u32) * 8 } else { 8 };
                let name = format!("input_{}", input_id);
                Ok(z3::ast::BV::new_const(ctx, name, n_bits).into())
            }
            OpKind::Add => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Add lhs not BV"))?
                    .bvadd(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Add rhs not BV"))?)
                    .into())
            }
            OpKind::Sub => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Sub lhs not BV"))?
                    .bvsub(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Sub rhs not BV"))?)
                    .into())
            }
            OpKind::Mul => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Mul lhs not BV"))?
                    .bvmul(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Mul rhs not BV"))?)
                    .into())
            }
            OpKind::Mulu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Mulu lhs not BV"))?
                    .bvmul(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Mulu rhs not BV"))?)
                    .into())
            }
            OpKind::Div => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Div lhs not BV"))?
                    .bvsdiv(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Div rhs not BV"))?)
                    .into())
            }
            OpKind::Divu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Divu lhs not BV"))?
                    .bvudiv(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Divu rhs not BV"))?)
                    .into())
            }
            OpKind::Rem => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Rem lhs not BV"))?
                    .bvsrem(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Rem rhs not BV"))?)
                    .into())
            }
            OpKind::Remu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Remu lhs not BV"))?
                    .bvurem(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Remu rhs not BV"))?)
                    .into())
            }
            OpKind::And => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
                    Ok(z3::ast::Bool::and(ctx, &[&lb, &rb]).into())
                } else {
                    Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("And lhs not BV/bool"))?
                        .bvand(&r.as_bv().ok_or_else(|| anyhow::anyhow!("And rhs not BV/bool"))?)
                        .into())
                }
            }
            OpKind::Or => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
                    Ok(z3::ast::Bool::or(ctx, &[&lb, &rb]).into())
                } else {
                    Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Or lhs not BV/bool"))?
                        .bvor(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Or rhs not BV/bool"))?)
                        .into())
                }
            }
            OpKind::Xor => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Xor lhs not BV"))?
                    .bvxor(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Xor rhs not BV"))?)
                    .into())
            }
            OpKind::Shl | OpKind::Sal => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Shl lhs not BV"))?
                    .bvshl(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Shl rhs not BV"))?)
                    .into())
            }
            OpKind::Shr => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Shr lhs not BV"))?
                    .bvlshr(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Shr rhs not BV"))?)
                    .into())
            }
            OpKind::Sar => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Sar lhs not BV"))?
                    .bvashr(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Sar rhs not BV"))?)
                    .into())
            }
            OpKind::Eq => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l._eq(&r).into())
            }
            OpKind::Ne => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l._eq(&r).not().into())
            }
            OpKind::Lt => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Lt lhs not BV"))?
                    .bvslt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Lt rhs not BV"))?)
                    .into())
            }
            OpKind::Le => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Le lhs not BV"))?
                    .bvsle(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Le rhs not BV"))?)
                    .into())
            }
            OpKind::Gt => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Gt lhs not BV"))?
                    .bvsgt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Gt rhs not BV"))?)
                    .into())
            }
            OpKind::Ge => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Ge lhs not BV"))?
                    .bvsge(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Ge rhs not BV"))?)
                    .into())
            }
            OpKind::Ltu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Ltu lhs not BV"))?
                    .bvult(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Ltu rhs not BV"))?)
                    .into())
            }
            OpKind::Leu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Leu lhs not BV"))?
                    .bvule(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Leu rhs not BV"))?)
                    .into())
            }
            OpKind::Gtu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Gtu lhs not BV"))?
                    .bvugt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Gtu rhs not BV"))?)
                    .into())
            }
            OpKind::Geu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Geu lhs not BV"))?
                    .bvuge(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Geu rhs not BV"))?)
                    .into())
            }
            OpKind::Extract => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Extract op1 not BV"))?;
                if expr.op2_is_const == 0 || expr.op3_is_const == 0 { anyhow::bail!("Extract requires const high/low indices") }
                let high = expr.op2 as u32;
                let low = expr.op3 as u32;
                Ok(bv.extract(high, low).into())
            }
            OpKind::Extract8 => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Extract8 op1 not BV"))?;
                if expr.op2_is_const == 0 { anyhow::bail!("Extract8 requires const byte index") }
                let byte_index = expr.op2 as u32;
                let high = ((byte_index + 1) * 8) - 1;
                let low = byte_index * 8;
                Ok(bv.extract(high, low).into())
            }
            OpKind::Concat => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Concat lhs not BV"))?
                    .concat(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Concat rhs not BV"))?)
                    .into())
            }
            OpKind::Zext => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Zext op1 not BV"))?;
                let target_bits = expr.op2 as u32;
                let cur = bv.get_size();
                let extend_by = if target_bits > cur { target_bits - cur } else { 0 };
                Ok(bv.zero_ext(extend_by).into())
            }
            OpKind::Sext => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Sext op1 not BV"))?;
                let target_bits = expr.op2 as u32;
                let cur = bv.get_size();
                let extend_by = if target_bits > cur { target_bits - cur } else { 0 };
                Ok(bv.sign_ext(extend_by).into())
            }
            // Memory/symbolic ops: model as fresh Z3 symbols to decouple from
            // concrete memory reasoning. Higher layers (MemorySliceReasoner) can
            // optionally add constraints relating these symbols.
            OpKind::MemorySlice => {
                let base = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let size = expr.op2 as u64;
                let base_bv = base.as_bv().ok_or_else(|| anyhow::anyhow!("MemorySlice base not BV"))?;
                let name = format!("slice_{}_{}", base_bv.to_string(), size);
                Ok(z3::ast::BV::new_const(ctx, name, (size * 8) as u32).into())
            }
            OpKind::SymbolicJumpTableAccess => {
                // Model as a fresh 64-bit address symbol. Higher layers may further constrain it.
                let name = format!("jt_access_{}", (expr as *const Expr as usize));
                Ok(z3::ast::BV::new_const(ctx, name, 64).into())
            }
            OpKind::SymbolicLoad => {
                let addr = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let addr_bv = addr.as_bv().ok_or_else(|| anyhow::anyhow!("SymbolicLoad addr not BV"))?;
                let name = format!("load_{}", addr_bv.to_string());
                Ok(z3::ast::BV::new_const(ctx, name, 64).into())
            }
            OpKind::SymbolicStore => {
                let _addr = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let val = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(val)
            }
            OpKind::Rotl => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let amount = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(op_bv), Some(amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    Ok(op_bv.bvrotl(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Rotl operation")
                }
            }
            OpKind::Rotr => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let amount = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(op_bv), Some(amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    Ok(op_bv.bvrotr(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Rotr operation")
                }
            }
            // i386-specific: delegate to i386 translator to mirror C routing
            OpKind::Rcl
            | OpKind::CmpEq | OpKind::CmpGt | OpKind::CmpGe | OpKind::CmpLt | OpKind::CmpLe
            | OpKind::Pmovmskb
            | OpKind::Min | OpKind::Max
            | OpKind::EflagsAllAdd | OpKind::EflagsAllAdcb | OpKind::EflagsAllAdcw | OpKind::EflagsAllAdcl | OpKind::EflagsAllAdcq
            | OpKind::EflagsAllSub | OpKind::EflagsAllMul | OpKind::EflagsAllSbbb | OpKind::EflagsAllSbbw | OpKind::EflagsAllSbbl | OpKind::EflagsAllSbbq
            | OpKind::EflagsAllLogic | OpKind::EflagsAllInc | OpKind::EflagsAllDec | OpKind::EflagsAllShl | OpKind::EflagsAllSar | OpKind::EflagsAllBmilg
            | OpKind::EflagsAllAdcx | OpKind::EflagsAllAdox | OpKind::EflagsAllAdcox | OpKind::EflagsAllRcl
            | OpKind::EflagsCAdd | OpKind::EflagsCAdcb | OpKind::EflagsCAdcw | OpKind::EflagsCAdcl | OpKind::EflagsCAdcq
            | OpKind::EflagsCSub | OpKind::EflagsCMul | OpKind::EflagsCSbbb | OpKind::EflagsCSbbw | OpKind::EflagsCSbbl | OpKind::EflagsCSbbq
            | OpKind::EflagsCLogic | OpKind::EflagsCShl => {
                let width = std::mem::size_of::<usize>();
                i386::smt_query_i386_to_z3(ctx, expr, width)
            }
            OpKind::IteEqZero => {
                // (ite (== op1 0) op2 op3) treating op1 as BV if needed
                let c = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let t = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                let e = Self::translate_operand_static(ctx, expr.op3, expr.op3_is_const)?;
                let cond = if let Some(cb) = c.as_bool() {
                    cb._eq(&z3::ast::Bool::from_bool(ctx, true)) // rarely used; prefer BV route
                } else if let Some(cbv) = c.as_bv() {
                    let zero = z3::ast::BV::from_u64(ctx, 0, cbv.get_size());
                    cbv._eq(&zero)
                } else {
                    anyhow::bail!("IteEqZero cond not BV/bool")
                };
                if let (Some(tbv), Some(ebv)) = (t.as_bv(), e.as_bv()) {
                    Ok(cond.ite(&tbv.into(), &ebv.into()))
                } else if let (Some(tb), Some(eb)) = (t.as_bool(), e.as_bool()) {
                    Ok(cond.ite(&tb.into(), &eb.into()))
                } else {
                    anyhow::bail!("IteEqZero branch types mismatch")
                }
            }
            OpKind::IteNeZero => {
                // (ite (!= op1 0) op2 op3)
                let c = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let t = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                let e = Self::translate_operand_static(ctx, expr.op3, expr.op3_is_const)?;
                let cond = if let Some(cb) = c.as_bool() {
                    cb // already boolean
                } else if let Some(cbv) = c.as_bv() {
                    let zero = z3::ast::BV::from_u64(ctx, 0, cbv.get_size());
                    cbv._eq(&zero).not()
                } else {
                    anyhow::bail!("IteNeZero cond not BV/bool")
                };
                if let (Some(tbv), Some(ebv)) = (t.as_bv(), e.as_bv()) {
                    Ok(cond.ite(&tbv.into(), &ebv.into()))
                } else if let (Some(tb), Some(eb)) = (t.as_bool(), e.as_bool()) {
                    Ok(cond.ite(&tb.into(), &eb.into()))
                } else {
                    anyhow::bail!("IteNeZero branch types mismatch")
                }
            }
            OpKind::Nand => {
                let left = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let right = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvand(&right_bv).bvnot().into())
                } else {
                    anyhow::bail!("Invalid operands for Nand operation")
                }
            }
            OpKind::Clz => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let op_bv = operand.as_bv().ok_or_else(|| anyhow::anyhow!("Invalid operand for Clz operation"))?;
                let n = op_bv.get_size();
                let zero_n = z3::ast::BV::from_u64(ctx, 0, n);
                let is_zero = op_bv._eq(&zero_n);
                // Build chain: if op==0 then n else first k where high k bits zero and next bit is 1
                let mut acc: z3::ast::Dynamic = z3::ast::BV::from_u64(ctx, n as u64, 64).into();
                for k in (0..n).rev() {
                    // high k bits zero
                    let high_zero = if k == 0 {
                        z3::ast::Bool::from_bool(ctx, true)
                    } else {
                        let hi = n - 1;
                        let lo = n - k;
                        let high = op_bv.extract(hi, lo);
                        high._eq(&z3::ast::BV::from_u64(ctx, 0, k))
                    };
                    let next_bit_index = n - k - 1;
                    let next_bit = op_bv.extract(next_bit_index, next_bit_index);
                    let next_is_one = next_bit._eq(&z3::ast::BV::from_u64(ctx, 1, 1));
                    let both = z3::ast::Bool::and(ctx, &[&high_zero, &next_is_one]);
                    let res_k = z3::ast::BV::from_u64(ctx, k as u64, 64);
                    acc = both.ite(&res_k.into(), &acc);
                }
                Ok(is_zero.ite(&z3::ast::BV::from_u64(ctx, n as u64, 64).into(), &acc))
            }
            _ => {
                anyhow::bail!(
                    "Unsupported OpKind {} in expression translation (translate.rs). This case is not yet implemented.",
                    expr.opkind
                )
            }
        }
    }
}
