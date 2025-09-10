use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::{SimplificationRule, get_const};

/// Safe multiplication by power of 2 rule - only for verified unsigned contexts
pub struct SafeMulPow2Rule;

impl SimplificationRule for SafeMulPow2Rule {
    fn name(&self) -> &str { "SafeMulPow2" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Mul) {
            return Ok(expr.clone());
        }
        
        if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
            // Only apply if we can verify this is an unsigned context
            // For now, be very conservative - only apply to small power-of-2 constants
            if let Some(val) = get_const(b) {
                if val.is_power_of_two() && val > 0 && val <= 256 { // Conservative limit
                    let shift_amount = val.trailing_zeros() as u64;
                    return Ok(Expr {
                        op1: a as *const Expr as *mut Expr,
                        op2: shift_amount as *mut Expr,
                        op3: std::ptr::null_mut(),
                        opkind: OpKind::Shl as u8,
                        op1_is_const: 0,
                        op2_is_const: 1,
                        op3_is_const: 0,
                    });
                }
            }
            if let Some(val) = get_const(a) {
                if val.is_power_of_two() && val > 0 && val <= 256 { // Conservative limit
                    let shift_amount = val.trailing_zeros() as u64;
                    return Ok(Expr {
                        op1: b as *const Expr as *mut Expr,
                        op2: shift_amount as *mut Expr,
                        op3: std::ptr::null_mut(),
                        opkind: OpKind::Shl as u8,
                        op1_is_const: 0,
                        op2_is_const: 1,
                        op3_is_const: 0,
                    });
                }
            }
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 115 }
}

/// Safe division and remainder by power of 2 rule - only for unsigned operations
pub struct SafeDivRemPow2Rule;

impl SimplificationRule for SafeDivRemPow2Rule {
    fn name(&self) -> &str { "SafeDivRemPow2" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        match expr.try_opkind().ok() {
            Some(OpKind::Divu) => { // Only unsigned division
                if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
                    if let Some(val) = get_const(b) {
                        if val.is_power_of_two() && val > 0 && val <= 256 { // Conservative
                            let shift_amount = val.trailing_zeros() as u64;
                            return Ok(Expr {
                                op1: a as *const Expr as *mut Expr,
                                op2: shift_amount as *mut Expr,
                                op3: std::ptr::null_mut(),
                                opkind: OpKind::Shr as u8,
                                op1_is_const: 0,
                                op2_is_const: 1,
                                op3_is_const: 0,
                            });
                        }
                    }
                }
            }
            Some(OpKind::Remu) => { // Only unsigned remainder
                if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
                    if let Some(val) = get_const(b) {
                        if val.is_power_of_two() && val > 0 && val <= 256 { // Conservative
                            let mask = val - 1;
                            return Ok(Expr {
                                op1: a as *const Expr as *mut Expr,
                                op2: mask as *mut Expr,
                                op3: std::ptr::null_mut(),
                                opkind: OpKind::And as u8,
                                op1_is_const: 0,
                                op2_is_const: 1,
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
    
    fn priority(&self) -> u32 { 116 }
}
