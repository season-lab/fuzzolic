use anyhow::Result;
use std::collections::HashMap;
use z3::ast::Ast;
use crate::expressions::expression::{Expr, OpKind};
use crate::expressions::expression_simplifier::ExpressionSimplifier;
use crate::expressions::arena::ArenaScope;
use crate::solver::SMTSolver;
use crate::solver::i386;

impl SMTSolver {
    /// Coerce a Bool into a bit-vector of given width: (bool ? 1 : 0) zero-extended
    fn bool_to_bv<'a>(ctx: &'a z3::Context, b: &z3::ast::Bool<'a>, width: u32) -> z3::ast::BV<'a> {
        let one_bv = z3::ast::BV::from_u64(ctx, 1, 1);
        let zero_bv = z3::ast::BV::from_u64(ctx, 0, 1);
        let one_dyn: z3::ast::Dynamic = one_bv.clone().into();
        let zero_dyn: z3::ast::Dynamic = zero_bv.clone().into();
        let bv1_dyn = b.ite(&one_dyn, &zero_dyn);
        let bv1 = bv1_dyn.as_bv().expect("Bool::ite should yield BV when branches are BV");
        if width > 1 { bv1.zero_ext(width - 1) } else { bv1 }
    }

    /// Coerce two BV operands to the same width.
    /// If one side is 64-bit and the other is narrower, prefer truncating the 64-bit side to the
    /// narrower width (to match common intent when constants are encoded as 64-bit immediates).
    /// Otherwise, zero-extend the narrower side to the wider width.
    fn coerce_bv_pair<'a>(l: z3::ast::BV<'a>, r: z3::ast::BV<'a>) -> (z3::ast::BV<'a>, z3::ast::BV<'a>) {
        let ls = l.get_size();
        let rs = r.get_size();
        if ls == rs { return (l, r); }
        // Prefer matching the smaller width when a 64-bit side is paired with a narrower one
        if ls == 64 && rs < 64 {
            let lt = l.extract(rs - 1, 0);
            return (lt, r);
        }
        if rs == 64 && ls < 64 {
            let rt = r.extract(ls - 1, 0);
            return (l, rt);
        }
        // Fallback: extend narrower to match wider
        if ls < rs { (l.zero_ext(rs - ls), r) } else { (l, r.zero_ext(ls - rs)) }
    }

    /// Top-level translator. Clears simplifier visit state ONCE per translation, then delegates.
    pub fn translate_expression_static<'a>(ctx: &'a z3::Context, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        // One-time init for this translation pass
        ExpressionSimplifier::clear_visit_state();
        let mut cache: HashMap<usize, z3::ast::Dynamic<'a>> = HashMap::new();
        // Perform full-tree simplification once to mirror C optimize_z3_query
        let _arena_scope = ArenaScope::enter();
        let mut simp = ExpressionSimplifier::new_conservative();
        log::info!("[SOLVER] Starting expression simplification");
        let s = simp.simplify_recursive(expr).unwrap_or_else(|_| expr.clone());
        log::info!("[SOLVER] Expression simplification completed");
        let d = Self::translate_expression_inner(ctx, &s, &mut cache)?;
        Ok(d)
        // Ok(d.simplify())
    }
    /// Helper: translate an operand that can be either a constant (embedded in the pointer)
    /// or a pointer to another Expr node. Mirrors the C-side encoding using op*_is_const flags.
    fn translate_operand_static<'a>(ctx: &'a z3::Context, operand: *mut Expr, is_const: u8, cache: &mut HashMap<usize, z3::ast::Dynamic<'a>>) -> Result<z3::ast::Dynamic<'a>> {
        let raw = operand as usize;
        if is_const != 0 {
            // Treat as immediate constant when the flag says so
            let value = operand as u64;
            return Ok(z3::ast::BV::from_u64(ctx, value, 64).into());
        }
        // Cache lookup for node pointers
        if let Some(d) = cache.get(&raw) { return Ok(d.clone()); }
        let res = match Expr::with_operand_ref_from_raw(is_const, operand, |e| Self::translate_expression_inner(ctx, e, cache)) {
            Some(r) => r,
            None => anyhow::bail!("Null (non-const) operand encountered in translation"),
        }?;
        cache.insert(raw, res.clone());
        Ok(res)
    }

    /// Recursive translator that avoids re-simplifying subtrees. Top-level performs simplification.
    fn translate_expression_inner<'a>(ctx: &'a z3::Context, expr: &Expr, cache: &mut HashMap<usize, z3::ast::Dynamic<'a>>) -> Result<z3::ast::Dynamic<'a>> {
        let op = expr.try_opkind()?;
        // Quick self-loop detection: compare child raw pointers against the original expr address
        let self_ptr = expr as *const Expr as usize;
        if expr.op1_is_const == 0 && (expr.op1 as usize) == self_ptr { anyhow::bail!("translate: self-loop on op1"); }
        if expr.op2_is_const == 0 && (expr.op2 as usize) == self_ptr { anyhow::bail!("translate: self-loop on op2"); }
        if expr.op3_is_const == 0 && (expr.op3 as usize) == self_ptr { anyhow::bail!("translate: self-loop on op3"); }
        match op {
            OpKind::Not => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                if let Some(b) = v.as_bool() { Ok(b.not().into()) } else { Ok(v.as_bv().ok_or_else(|| anyhow::anyhow!("Not op1 not BV/bool"))?.bvnot().into()) }
            }
            OpKind::Neg => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
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
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Add lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Add rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvadd(&rco).into())
            }
            OpKind::Sub => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Sub lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Sub rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvsub(&rco).into())
            }
            OpKind::Mul => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Mul lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Mul rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvmul(&rco).into())
            }
            OpKind::Mulu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Mulu lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Mulu rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvmul(&rco).into())
            }
            OpKind::Div => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Div lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Div rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvsdiv(&rco).into())
            }
            OpKind::Divu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Divu lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Divu rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvudiv(&rco).into())
            }
            OpKind::Rem => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Rem lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Rem rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvsrem(&rco).into())
            }
            OpKind::Remu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Remu lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Remu rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvurem(&rco).into())
            }
            OpKind::And => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
                    Ok(z3::ast::Bool::and(ctx, &[&lb, &rb]).into())
                } else {
                    let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("And lhs not BV/bool"))?;
                    let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("And rhs not BV/bool"))?;
                    let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                    Ok(lco.bvand(&rco).into())
                }
            }
            OpKind::Or => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
                    Ok(z3::ast::Bool::or(ctx, &[&lb, &rb]).into())
                } else {
                    let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Or lhs not BV/bool"))?;
                    let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Or rhs not BV/bool"))?;
                    let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                    Ok(lco.bvor(&rco).into())
                }
            }
            OpKind::Xor => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Xor lhs not BV"))?;
                let rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Xor rhs not BV"))?;
                let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                Ok(lco.bvxor(&rco).into())
            }
            OpKind::Shl | OpKind::Sal => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Shl lhs not BV"))?;
                let mut rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Shl rhs not BV"))?;
                let ls = lbv.get_size();
                let rs = rbv.get_size();
                if rs < ls { rbv = rbv.zero_ext(ls - rs); }
                else if rs > ls { rbv = rbv.extract(ls - 1, 0); }
                Ok(lbv.bvshl(&rbv).into())
            }
            OpKind::Shr => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Shr lhs not BV"))?;
                let mut rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Shr rhs not BV"))?;
                let ls = lbv.get_size();
                let rs = rbv.get_size();
                if rs < ls { rbv = rbv.zero_ext(ls - rs); }
                else if rs > ls { rbv = rbv.extract(ls - 1, 0); }
                Ok(lbv.bvlshr(&rbv).into())
            }
            OpKind::Sar => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let lbv = l.as_bv().ok_or_else(|| anyhow::anyhow!("Sar lhs not BV"))?;
                let mut rbv = r.as_bv().ok_or_else(|| anyhow::anyhow!("Sar rhs not BV"))?;
                let ls = lbv.get_size();
                let rs = rbv.get_size();
                if rs < ls { rbv = rbv.zero_ext(ls - rs); }
                else if rs > ls { rbv = rbv.extract(ls - 1, 0); }
                Ok(lbv.bvashr(&rbv).into())
            }
            OpKind::Eq => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                match (l.as_bool(), r.as_bool(), l.as_bv(), r.as_bv()) {
                    (Some(lb), Some(rb), _, _) => Ok(lb._eq(&rb).into()),
                    (_, _, Some(lbv), Some(rbv)) => {
                        let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                        Ok(lco._eq(&rco).into())
                    }
                    (Some(lb), _, _, Some(rbv)) => {
                        let ls = rbv.get_size();
                        let lco = Self::bool_to_bv(ctx, &lb, ls);
                        Ok(lco._eq(&rbv).into())
                    }
                    (_, Some(rb), Some(lbv), _) => {
                        let rs = lbv.get_size();
                        let rco = Self::bool_to_bv(ctx, &rb, rs);
                        Ok(lbv._eq(&rco).into())
                    }
                    _ => anyhow::bail!("Eq operands not coercible to compatible sorts"),
                }
            }
            OpKind::Ne => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let res_dyn = match (l.as_bool(), r.as_bool(), l.as_bv(), r.as_bv()) {
                    (Some(lb), Some(rb), _, _) => lb._eq(&rb).not().into(),
                    (_, _, Some(lbv), Some(rbv)) => {
                        let (lco, rco) = Self::coerce_bv_pair(lbv, rbv);
                        lco._eq(&rco).not().into()
                    }
                    (Some(lb), _, _, Some(rbv)) => {
                        let ls = rbv.get_size();
                        let lco = Self::bool_to_bv(ctx, &lb, ls);
                        lco._eq(&rbv).not().into()
                    }
                    (_, Some(rb), Some(lbv), _) => {
                        let rs = lbv.get_size();
                        let rco = Self::bool_to_bv(ctx, &rb, rs);
                        lbv._eq(&rco).not().into()
                    }
                    _ => anyhow::bail!("Ne operands not coercible to compatible sorts"),
                };
                Ok(res_dyn)
            }
            OpKind::Lt => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Lt lhs not BV"))?
                    .bvslt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Lt rhs not BV"))?)
                    .into())
            }
            OpKind::Le => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Le lhs not BV"))?
                    .bvsle(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Le rhs not BV"))?)
                    .into())
            }
            OpKind::Gt => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Gt lhs not BV"))?
                    .bvsgt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Gt rhs not BV"))?)
                    .into())
            }
            OpKind::Ge => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Ge lhs not BV"))?
                    .bvsge(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Ge rhs not BV"))?)
                    .into())
            }
            OpKind::Ltu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Ltu lhs not BV"))?
                    .bvult(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Ltu rhs not BV"))?)
                    .into())
            }
            OpKind::Leu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Leu lhs not BV"))?
                    .bvule(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Leu rhs not BV"))?)
                    .into())
            }
            OpKind::Gtu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Gtu lhs not BV"))?
                    .bvugt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Gtu rhs not BV"))?)
                    .into())
            }
            OpKind::Geu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Geu lhs not BV"))?
                    .bvuge(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Geu rhs not BV"))?)
                    .into())
            }
            OpKind::Extract => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Extract op1 not BV"))?;
                // Accept either split (op2=high, op3=low) or packed in op2 (high,low)
                let (mut high, mut low) = if expr.op2_is_const != 0 && expr.op3_is_const != 0 {
                    (expr.op2 as u32, expr.op3 as u32)
                } else if expr.op2_is_const != 0 {
                    // Packed form
                    let (h, l) = {
                        // Reuse same packing as simplifier: upper 32 bits at higher address bits
                        crate::expressions::expression::Expr::unpack_u32_pair_from_ptr(expr.op2)
                    };
                    (h, l)
                } else {
                    anyhow::bail!("Extract missing constant indices (neither split nor packed)")
                };
                let sz = bv.get_size();
                if sz == 0 { anyhow::bail!("Extract on zero-width BV") }
                if high >= sz { high = sz - 1; }
                if low > high { low = high; }
                Ok(bv.extract(high, low).into())
            }
            OpKind::Extract8 => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Extract8 op1 not BV"))?;
                // C semantics: treat op2 as the byte index immediate (no flag check)
                let byte_index: u32 = expr.op2 as u32;
                let sz = bv.get_size();
                if sz == 0 { anyhow::bail!("Extract8 on zero-width BV") }
                // Clamp index within available bytes
                let max_idx = (sz.saturating_sub(1)) / 8;
                let idx = if byte_index > max_idx { max_idx } else { byte_index };
                let high = ((idx + 1) * 8).saturating_sub(1);
                let low = idx * 8;
                Ok(bv.extract(high, low).into())
            }
            OpKind::Concat => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Concat lhs not BV"))?
                    .concat(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Concat rhs not BV"))?)
                    .into())
            }
            // Concat8R/Concat8L: append an 8-bit piece to the right/left of an existing bitvector
            OpKind::Concat8R => {
                // Correct operand order: op1 is the existing BV (high bits), op2 is the new 8-bit piece (low bits)
                let left = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;  // existing BV
                let right = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?; // 8-bit piece to append
                let lbv = left.as_bv().ok_or_else(|| anyhow::anyhow!("Concat8R left not BV"))?;
                let mut rbv = right.as_bv().ok_or_else(|| anyhow::anyhow!("Concat8R right not BV"))?;
                // Ensure right is exactly 8 bits
                let rsz = rbv.get_size();
                if rsz > 8 { rbv = rbv.extract(7, 0); }
                else if rsz < 8 { rbv = rbv.zero_ext(8 - rsz); }
                Ok(lbv.concat(&rbv).into())
            }
            OpKind::Concat8L => {
                let left = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?; // 8-bit piece to prepend (high bits)
                let right = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?; // existing BV (low bits)
                let mut lbv = left.as_bv().ok_or_else(|| anyhow::anyhow!("Concat8L left not BV"))?;
                let rbv = right.as_bv().ok_or_else(|| anyhow::anyhow!("Concat8L right not BV"))?;
                // Ensure left is exactly 8 bits
                let lsz = lbv.get_size();
                if lsz > 8 { lbv = lbv.extract(7, 0); }
                else if lsz < 8 { lbv = lbv.zero_ext(8 - lsz); }
                Ok(lbv.concat(&rbv).into())
            }
            OpKind::Zext => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Zext op1 not BV"))?;
                let target_bits = expr.op2 as u32;
                let cur = bv.get_size();
                if target_bits > cur {
                    Ok(bv.zero_ext(target_bits - cur).into())
                } else {
                    Ok(bv.into())
                }
            }
            OpKind::Sext => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Sext op1 not BV"))?;
                let target_bits = expr.op2 as u32;
                let cur = bv.get_size();
                if target_bits > cur {
                    Ok(bv.sign_ext(target_bits - cur).into())
                } else {
                    Ok(bv.into())
                }
            }
            // Memory/symbolic ops: model as fresh Z3 symbols to decouple from
            // concrete memory reasoning. Higher layers (MemorySliceReasoner) can
            // optionally add constraints relating these symbols.
            OpKind::MemorySlice => {
                let base = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
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
                let _addr = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                // Avoid depending on AST stringification for names; use pointer identity instead.
                let name = format!("load_{:x}", expr.op1 as usize);
                Ok(z3::ast::BV::new_const(ctx, name, 64).into())
            }
            OpKind::SymbolicStore => {
                let _addr = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let val = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                Ok(val)
            }
            OpKind::Rotl => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let amount = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                if let (Some(op_bv), Some(mut amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    let ls = op_bv.get_size();
                    let rs = amt_bv.get_size();
                    if rs < ls { amt_bv = amt_bv.zero_ext(ls - rs); }
                    else if rs > ls { amt_bv = amt_bv.extract(ls - 1, 0); }
                    Ok(op_bv.bvrotl(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Rotl operation")
                }
            }
            OpKind::Rotr => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let amount = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                if let (Some(op_bv), Some(mut amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    let ls = op_bv.get_size();
                    let rs = amt_bv.get_size();
                    if rs < ls { amt_bv = amt_bv.zero_ext(ls - rs); }
                    else if rs > ls { amt_bv = amt_bv.extract(ls - 1, 0); }
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
                let c = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let t = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let e = Self::translate_operand_static(ctx, expr.op3, expr.op3_is_const, cache)?;
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
                let c = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let t = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                let e = Self::translate_operand_static(ctx, expr.op3, expr.op3_is_const, cache)?;
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
                let left = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
                let right = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const, cache)?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    let (lco, rco) = Self::coerce_bv_pair(left_bv, right_bv);
                    Ok(lco.bvand(&rco).bvnot().into())
                } else {
                    anyhow::bail!("Invalid operands for Nand operation")
                }
            }
            OpKind::Clz => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const, cache)?;
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
