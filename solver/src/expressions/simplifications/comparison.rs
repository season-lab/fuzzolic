use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::{SimplificationRule, get_const};

/// DEPRECATED: Equality over zero-extend rule - potentially unsafe
/// This rule is disabled as it may not preserve semantics with signed/unsigned differences
pub struct EqOverZextRule;

impl SimplificationRule for EqOverZextRule {
    fn name(&self) -> &str { "EqOverZext" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        // DISABLED: Zero-extension equality optimizations can be unsafe
        // They may not preserve semantics when dealing with signed vs unsigned operations
        Ok(expr.clone())
    }

    fn priority(&self) -> u32 { 129 }
}

/// Equality identity rule - handles X == X and constant comparisons
pub struct EqIdentityRule;

impl SimplificationRule for EqIdentityRule {
    fn name(&self) -> &str { "EqIdentity" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Eq) || expr.safe_op1_ref().is_none() || expr.safe_op2_ref().is_none() {
            return Ok(expr.clone());
        }
        
        let a = expr.safe_op1_ref().unwrap();
        let b = expr.safe_op2_ref().unwrap();
        
        // REMOVED: Pointer equality check (unsafe with structural equality)
        
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
                if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
                    // Sub(x, y) == 0 => x == y
                    if a.opkind_is(OpKind::Sub) && get_const(b) == Some(0) {
                        if let (Some(x), Some(y)) = (a.safe_op1_ref(), a.safe_op2_ref()) {
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
                        if let (Some(x), Some(y)) = (b.safe_op1_ref(), b.safe_op2_ref()) {
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
