use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::{SimplificationRule, get_const};

/// Double negation: not(not(x)) => x
pub struct NotNotEliminateRule;

impl SimplificationRule for NotNotEliminateRule {
    fn name(&self) -> &str { "NotNotEliminate" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Not) { return Ok(expr.clone()); }
        let a = if let Some(x) = expr.op1_ref() { x } else { return Ok(expr.clone()); };
        if a.opkind_is(OpKind::Not) {
            if let Some(inner) = a.op1_ref() { return Ok(inner.clone()); }
        }
        Ok(expr.clone())
    }

    fn priority(&self) -> u32 { 119 }
}

/// Boolean simplification rule - handles NOT operations on constants
pub struct BooleanSimplificationRule;

impl SimplificationRule for BooleanSimplificationRule {
    fn name(&self) -> &str { "BooleanSimplification" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        match expr.try_opkind().ok() {
            Some(OpKind::Not) => {
                if let Some(op1) = expr.op1_ref() {
                    if let Some(val) = get_const(op1) {
                        let result = if val == 0 { 1u64 } else { 0u64 };
                        return Ok(Expr {
                            op1: result as *mut Expr,
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
            _ => {}
        }
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 100 }
}

/// NOT simplification rule - handles NOT operations on constants
pub struct NotSimplificationRule;

impl SimplificationRule for NotSimplificationRule {
    fn name(&self) -> &str { "NotSimplification" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Not) || expr.op1_ref().is_none() {
            return Ok(expr.clone());
        }
        
        let a = expr.op1_ref().unwrap();
        if let Some(v) = get_const(a) {
            let r = if v == 0 { 1u64 } else { 0u64 };
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
    
    fn priority(&self) -> u32 { 110 }
}
