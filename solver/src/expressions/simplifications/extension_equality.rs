use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::{SimplificationRule, get_const};

/// Safe zero-extension equality rule - only for clearly safe cases
pub struct SafeZextEqualityRule;

impl SimplificationRule for SafeZextEqualityRule {
    fn name(&self) -> &str { "SafeZextEquality" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Eq) || expr.safe_op1_ref().is_none() || expr.safe_op2_ref().is_none() {
            return Ok(expr.clone());
        }
        let a = expr.safe_op1_ref().unwrap();
        let b = expr.safe_op2_ref().unwrap();

        // Only handle the safest case: eq(zext(x), 0) => eq(x, 0)
        // This is always safe regardless of signedness
        if a.opkind_is(OpKind::Zext) {
            if get_const(b) == Some(0) {
                if let Some(inner) = a.safe_op1_ref() {
                    return Ok(Expr {
                        op1: inner as *const Expr as *mut Expr,
                        op2: b as *const Expr as *mut Expr,
                        op3: std::ptr::null_mut(),
                        opkind: OpKind::Eq as u8,
                        op1_is_const: 0,
                        op2_is_const: 1,
                        op3_is_const: 0,
                    });
                }
            }
        }
        if b.opkind_is(OpKind::Zext) {
            if get_const(a) == Some(0) {
                if let Some(inner) = b.safe_op1_ref() {
                    return Ok(Expr {
                        op1: inner as *const Expr as *mut Expr,
                        op2: a as *const Expr as *mut Expr,
                        op3: std::ptr::null_mut(),
                        opkind: OpKind::Eq as u8,
                        op1_is_const: 0,
                        op2_is_const: 1,
                        op3_is_const: 0,
                    });
                }
            }
        }

        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 117 }
}
