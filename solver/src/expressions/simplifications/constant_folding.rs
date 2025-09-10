use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::{SimplificationRule, get_const};

/// Constant folding rule - evaluates expressions with constant operands
pub struct ConstantFoldingRule;

impl SimplificationRule for ConstantFoldingRule {
    fn name(&self) -> &str { "ConstantFolding" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        match expr.try_opkind().ok() {
            Some(OpKind::Add) => {
                if expr.op1_is_const != 0 && expr.op2_is_const != 0 {
                    let a = expr.op1 as u64;
                    let b = expr.op2 as u64;
                    let result = a.wrapping_add(b);
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
            Some(OpKind::Sub) => {
                if expr.op1_is_const != 0 && expr.op2_is_const != 0 {
                    let a = expr.op1 as u64;
                    let b = expr.op2 as u64;
                    let result = a.wrapping_sub(b);
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
            Some(OpKind::Mul) => {
                if expr.op1_is_const != 0 && expr.op2_is_const != 0 {
                    let a = expr.op1 as u64;
                    let b = expr.op2 as u64;
                    let result = a.wrapping_mul(b);
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
            Some(OpKind::And) => {
                if expr.op1_is_const != 0 && expr.op2_is_const != 0 {
                    let a = expr.op1 as u64;
                    let b = expr.op2 as u64;
                    let result = a & b;
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
            Some(OpKind::Or) => {
                if expr.op1_is_const != 0 && expr.op2_is_const != 0 {
                    let a = expr.op1 as u64;
                    let b = expr.op2 as u64;
                    let result = a | b;
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
            Some(OpKind::Xor) => {
                if expr.op1_is_const != 0 && expr.op2_is_const != 0 {
                    let a = expr.op1 as u64;
                    let b = expr.op2 as u64;
                    let result = a ^ b;
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
            Some(OpKind::Extract) => {
                if let Some(op1) = expr.safe_op1_ref() {
                    if let Some(val) = get_const(op1) {
                        let (high, low) = Expr::unpack_u32_pair_from_ptr(expr.op2);
                        let width = high - low + 1;
                        if width <= 64 {
                            let mask = if width == 64 { u64::MAX } else { (1u64 << width) - 1 };
                            let result = (val >> low) & mask;
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
            }
            _ => {}
        }
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 90 } // High priority for constant folding
}
