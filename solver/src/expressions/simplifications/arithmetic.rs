use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::{SimplificationRule, get_const};

/// Arithmetic simplification rule - handles basic arithmetic operations
pub struct ArithmeticSimplificationRule;

impl SimplificationRule for ArithmeticSimplificationRule {
    fn name(&self) -> &str { "ArithmeticSimplification" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        match expr.try_opkind().ok() {
            Some(OpKind::Add) => {
                if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
                    // 0 + X = X
                    if get_const(a) == Some(0) {
                        return Ok(b.clone());
                    }
                    // X + 0 = X
                    if get_const(b) == Some(0) {
                        return Ok(a.clone());
                    }
                    // Constant folding
                    if let (Some(va), Some(vb)) = (get_const(a), get_const(b)) {
                        let result = va.wrapping_add(vb);
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
            Some(OpKind::Sub) => {
                if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
                    // X - 0 = X
                    if get_const(b) == Some(0) {
                        return Ok(a.clone());
                    }
                    // REMOVED: X - X = 0 (unsafe with pointer equality)
                    // Constant folding
                    if let (Some(va), Some(vb)) = (get_const(a), get_const(b)) {
                        let result = va.wrapping_sub(vb);
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
            Some(OpKind::Mul) => {
                if let (Some(a), Some(b)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
                    // 0 * X = 0
                    if get_const(a) == Some(0) || get_const(b) == Some(0) {
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
                    // 1 * X = X
                    if get_const(a) == Some(1) {
                        return Ok(b.clone());
                    }
                    // X * 1 = X
                    if get_const(b) == Some(1) {
                        return Ok(a.clone());
                    }
                    // Constant folding
                    if let (Some(va), Some(vb)) = (get_const(a), get_const(b)) {
                        let result = va.wrapping_mul(vb);
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
    
    fn priority(&self) -> u32 { 105 }
}

/// Subtraction transform rule
pub struct SubtractionTransformRule;

impl SimplificationRule for SubtractionTransformRule {
    fn name(&self) -> &str { "SubtractionTransform" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        // This rule can handle more complex subtraction transformations
        // For now, basic functionality is covered by ArithmeticSimplificationRule
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 108 }
}

/// Arithmetic extract rule
pub struct ArithmeticExtractRule;

impl SimplificationRule for ArithmeticExtractRule {
    fn name(&self) -> &str { "ArithmeticExtract" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        // Handle extract operations on arithmetic results
        // This can be expanded to handle specific patterns
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 122 }
}

/// DEPRECATED: Multiplication by power of 2 rule - potentially unsafe
/// This rule is disabled as it may not preserve semantics in all contexts
pub struct MulPow2Rule;

impl SimplificationRule for MulPow2Rule {
    fn name(&self) -> &str { "MulPow2" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        // DISABLED: This optimization may not be safe in all contexts
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 115 }
}

/// DEPRECATED: Division and remainder by power of 2 rule - potentially unsafe
/// This rule is disabled as x % 2^n != x & (2^n-1) for signed integers
pub struct DivRemPow2Rule;

impl SimplificationRule for DivRemPow2Rule {
    fn name(&self) -> &str { "DivRemPow2" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        // DISABLED: x % 2^n != x & (2^n-1) for signed integers
        // This optimization is only valid for unsigned operations
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 116 }
}
