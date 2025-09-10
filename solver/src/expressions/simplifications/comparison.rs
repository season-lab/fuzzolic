use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::{SimplificationRule, get_const, infer_size};

/// Equality over zero-extend: simplifies eq(zext(x), 0) => eq(x, 0), and
/// eq(zext(x), zext(y)) => eq(x, y) when widths match; also eq(zext(x), C) => eq(x, C) if C fits.
pub struct EqOverZextRule;

impl SimplificationRule for EqOverZextRule {
    fn name(&self) -> &str { "EqOverZext" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Eq) || expr.op1_ref().is_none() || expr.op2_ref().is_none() {
            return Ok(expr.clone());
        }
        let a = expr.op1_ref().unwrap();
        let b = expr.op2_ref().unwrap();

        // Helper to build Eq with possibly constant rhs reused
        let mk_eq = |lhs: &Expr, rhs: &Expr, rhs_is_const: u8| -> Expr {
            Expr { op1: lhs as *const Expr as *mut Expr, op2: rhs as *const Expr as *mut Expr, op3: std::ptr::null_mut(), opkind: OpKind::Eq as u8, op1_is_const: 0, op2_is_const: rhs_is_const, op3_is_const: 0 }
        };

        // eq(zext(x), 0) or eq(0, zext(x)) => eq(x, 0)
        if a.opkind_is(OpKind::Zext) {
            if get_const(b) == Some(0) {
                if let Some(inner) = a.op1_ref() { return Ok(mk_eq(inner, b, 1)); }
            }
        }
        if b.opkind_is(OpKind::Zext) {
            if get_const(a) == Some(0) {
                if let Some(inner) = b.op1_ref() { return Ok(mk_eq(inner, a, 1)); }
            }
        }

        // eq(zext(x), zext(y)) => eq(x, y) if widths of x and y are equal and known
        if a.opkind_is(OpKind::Zext) && b.opkind_is(OpKind::Zext) {
            if let (Some(ax), Some(by)) = (a.op1_ref(), b.op1_ref()) {
                if let (Some(wa), Some(wb)) = (infer_size(ax), infer_size(by)) {
                    if wa == wb { return Ok(Expr { op1: ax as *const Expr as *mut Expr, op2: by as *const Expr as *mut Expr, op3: std::ptr::null_mut(), opkind: OpKind::Eq as u8, op1_is_const: 0, op2_is_const: 0, op3_is_const: 0 }); }
                }
            }
        }

        // eq(zext(x), C) when C fits into width(x) => eq(x, C)
        if a.opkind_is(OpKind::Zext) {
            if let Some(c) = get_const(b) {
                if let Some(inner) = a.op1_ref() {
                    if let Some(w) = infer_size(inner) {
                        let fits = if w >= 64 { true } else { c < (1u64 << w) };
                        if fits { return Ok(Expr { op1: inner as *const Expr as *mut Expr, op2: b as *const Expr as *mut Expr, op3: std::ptr::null_mut(), opkind: OpKind::Eq as u8, op1_is_const: 0, op2_is_const: 1, op3_is_const: 0 }); }
                    }
                }
            }
        }
        if b.opkind_is(OpKind::Zext) {
            if let Some(c) = get_const(a) {
                if let Some(inner) = b.op1_ref() {
                    if let Some(w) = infer_size(inner) {
                        let fits = if w >= 64 { true } else { c < (1u64 << w) };
                        if fits { return Ok(Expr { op1: inner as *const Expr as *mut Expr, op2: a as *const Expr as *mut Expr, op3: std::ptr::null_mut(), opkind: OpKind::Eq as u8, op1_is_const: 0, op2_is_const: 1, op3_is_const: 0 }); }
                    }
                }
            }
        }

        Ok(expr.clone())
    }

    fn priority(&self) -> u32 { 129 }
}

/// Equality identity rule - handles X == X and constant comparisons
pub struct EqIdentityRule;

impl SimplificationRule for EqIdentityRule {
    fn name(&self) -> &str { "EqIdentity" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Eq) || expr.op1_ref().is_none() || expr.op2_ref().is_none() {
            return Ok(expr.clone());
        }
        
        let a = expr.op1_ref().unwrap();
        let b = expr.op2_ref().unwrap();
        
        // Check if operands are identical (same pointer and opkind)
        if (expr.op1 as usize) == (expr.op2 as usize) && a.opkind == b.opkind {
            return Ok(Expr {
                op1: 1usize as *mut Expr,
                op2: std::ptr::null_mut(),
                op3: std::ptr::null_mut(),
                opkind: OpKind::IsConst as u8,
                op1_is_const: 1,
                op2_is_const: 0,
                op3_is_const: 0,
            });
        }
        
        // Handle constant comparisons
        if let (Some(va), Some(vb)) = (get_const(a), get_const(b)) {
            let r = if va == vb { 1u64 } else { 0u64 };
            return Ok(Expr {
                op1: r as *mut Expr,
                op2: std::ptr::null_mut(),
                op3: std::ptr::null_mut(),
                opkind: OpKind::IsConst as u8,
                op1_is_const: 1,
                op2_is_const: 0,
                op3_is_const: 0,
            });
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 120 }
}

/// Comparison optimization rule - handles various comparison simplifications
pub struct ComparisonOptimizationRule;

impl SimplificationRule for ComparisonOptimizationRule {
    fn name(&self) -> &str { "ComparisonOptimization" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        match expr.try_opkind().ok() {
            Some(OpKind::Eq) => {
                if let (Some(a), Some(b)) = (expr.op1_ref(), expr.op2_ref()) {
                    // Sub(x, y) == 0 => x == y
                    if a.opkind_is(OpKind::Sub) && get_const(b) == Some(0) {
                        if let (Some(x), Some(y)) = (a.op1_ref(), a.op2_ref()) {
                            return Ok(Expr {
                                op1: x as *const Expr as *mut Expr,
                                op2: y as *const Expr as *mut Expr,
                                op3: std::ptr::null_mut(),
                                opkind: OpKind::Eq as u8,
                                op1_is_const: 0,
                                op2_is_const: 0,
                                op3_is_const: 0,
                            });
                        }
                    }
                    // 0 == Sub(x, y) => x == y
                    if b.opkind_is(OpKind::Sub) && get_const(a) == Some(0) {
                        if let (Some(x), Some(y)) = (b.op1_ref(), b.op2_ref()) {
                            return Ok(Expr {
                                op1: x as *const Expr as *mut Expr,
                                op2: y as *const Expr as *mut Expr,
                                op3: std::ptr::null_mut(),
                                opkind: OpKind::Eq as u8,
                                op1_is_const: 0,
                                op2_is_const: 0,
                                op3_is_const: 0,
                            });
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 125 }
}
