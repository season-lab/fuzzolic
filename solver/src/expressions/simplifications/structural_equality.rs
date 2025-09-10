use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::SimplificationRule;

/// Safe structural equality rule - uses deep comparison instead of pointer equality
/// This avoids crashes from invalid pointer comparisons while still optimizing X - X = 0, etc.
pub struct SafeStructuralEqualityRule;

impl SimplificationRule for SafeStructuralEqualityRule {
    fn name(&self) -> &str { "SafeStructuralEquality" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        match expr.try_opkind().ok() {
            Some(OpKind::Sub) | Some(OpKind::Xor) => {
                if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
                    if self.deep_structural_equal(a, b, 0) {
                        // X - X = 0, X ^ X = 0
                        return Ok(Expr {
                            op1: 0 as *mut Expr,
                            op2: std::ptr::null_mut(),
                            op3: std::ptr::null_mut(),
                            opkind: OpKind::IsConst as u8,
                            op1_is_const: 1,
                            op2_is_const: 0,
                            op3_is_const: 0,
                        });
                    }
                }
            }
            Some(OpKind::And) | Some(OpKind::Or) => {
                if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
                    if self.deep_structural_equal(a, b, 0) {
                        // X & X = X, X | X = X
                        return Ok(Expr {
                            op1: a as *const Expr as *mut Expr,
                            op2: std::ptr::null_mut(),
                            op3: std::ptr::null_mut(),
                            opkind: a.opkind,
                            op1_is_const: a.op1_is_const,
                            op2_is_const: 0,
                            op3_is_const: 0,
                        });
                    }
                }
            }
            _ => {}
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 120 }
}

impl SafeStructuralEqualityRule {
    /// Deep structural equality check with cycle detection
    fn deep_structural_equal(&self, a: &Expr, b: &Expr, depth: u32) -> bool {
        // Prevent infinite recursion
        if depth > 20 {
            return false;
        }
        
        // Basic structure must match
        if a.opkind != b.opkind {
            return false;
        }
        if a.op1_is_const != b.op1_is_const {
            return false;
        }
        if a.op2_is_const != b.op2_is_const {
            return false;
        }
        if a.op3_is_const != b.op3_is_const {
            return false;
        }
        
        // Compare constant operands
        if a.op1_is_const != 0 && a.op1 != b.op1 { return false; }
        if a.op2_is_const != 0 && a.op2 != b.op2 { return false; }
        if a.op3_is_const != 0 && a.op3 != b.op3 { return false; }
        
        // Recursively compare non-constant operands
        if a.op1_is_const == 0 {
            match (a.safe_op1_ref(), b.safe_op1_ref()) {
                (Some(a1), Some(b1)) => {
                    if !self.deep_structural_equal(a1, b1, depth + 1) {
                        return false;
                    }
                }
                (None, None) => {}
                _ => return false,
            }
        }
        
        if a.op2_is_const == 0 {
            match (a.safe_op2_ref(), b.safe_op2_ref()) {
                (Some(a2), Some(b2)) => {
                    if !self.deep_structural_equal(a2, b2, depth + 1) {
                        return false;
                    }
                }
                (None, None) => {}
                _ => return false,
            }
        }
        
        if a.op3_is_const == 0 {
            match (a.safe_op3_ref(), b.safe_op3_ref()) {
                (Some(a3), Some(b3)) => {
                    if !self.deep_structural_equal(a3, b3, depth + 1) {
                        return false;
                    }
                }
                (None, None) => {}
                _ => return false,
            }
        }
        
        true
    }
}
