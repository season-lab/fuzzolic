use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::{SimplificationRule, get_const, infer_size};

/// Extract optimization rule - handles various extract simplifications
pub struct ExtractOptimizationRule;

impl SimplificationRule for ExtractOptimizationRule {
    fn name(&self) -> &str { "ExtractOptimization" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Extract) {
            return Ok(expr.clone());
        }
        
        let op1 = if let Some(op) = expr.op1_ref() { op } else { return Ok(expr.clone()); };
        let (high, low) = Expr::unpack_u32_pair_from_ptr(expr.op2);
        
        // Extract from constant
        if let Some(val) = get_const(op1) {
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
        
        // Extract of Extract - combine ranges
        if op1.opkind_is(OpKind::Extract) && op1.op2_is_const != 0 {
            let inner = op1.op1_ref().unwrap();
            let (_inner_high, inner_low) = Expr::unpack_u32_pair_from_ptr(op1.op2);
            let new_high = inner_low + high;
            let new_low = inner_low + low;
            let new_params = Expr::pack_u32_pair_to_ptr(new_high, new_low);
            return Ok(Expr {
                op1: inner as *const Expr as *mut Expr,
                op2: new_params,
                op3: std::ptr::null_mut(),
                opkind: OpKind::Extract as u8,
                op1_is_const: 0,
                op2_is_const: 1,
                op3_is_const: 0,
            });
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 115 }
}

/// Extract identity rule - removes redundant extracts
pub struct ExtractIdentityRule;

impl SimplificationRule for ExtractIdentityRule {
    fn name(&self) -> &str { "ExtractIdentity" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Extract) {
            return Ok(expr.clone());
        }
        
        let op1 = if let Some(op) = expr.op1_ref() { op } else { return Ok(expr.clone()); };
        let (high, low) = Expr::unpack_u32_pair_from_ptr(expr.op2);
        
        // Check if this is a full-width extract
        if let Some(width) = infer_size(op1) {
            if low == 0 && high + 1 == width {
                return Ok(op1.clone());
            }
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 118 }
}

/// Extract byte to Extract8 conversion rule
pub struct ExtractByteToExtract8Rule;

impl SimplificationRule for ExtractByteToExtract8Rule {
    fn name(&self) -> &str { "ExtractByteToExtract8" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Extract) {
            return Ok(expr.clone());
        }
        
        let op1 = if let Some(op) = expr.op1_ref() { op } else { return Ok(expr.clone()); };
        let (high, low) = Expr::unpack_u32_pair_from_ptr(expr.op2);
        
        // Check if this is an 8-bit aligned extract
        if (high - low + 1) == 8 && (low % 8) == 0 {
            let byte_index = low / 8;
            return Ok(Expr {
                op1: op1 as *const Expr as *mut Expr,
                op2: byte_index as *mut Expr,
                op3: std::ptr::null_mut(),
                opkind: OpKind::Extract8 as u8,
                op1_is_const: 0,
                op2_is_const: 1,
                op3_is_const: 0,
            });
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 112 }
}

/// Extract8 over zero-extend rule
pub struct Extract8OverZextRule;

impl SimplificationRule for Extract8OverZextRule {
    fn name(&self) -> &str { "Extract8OverZext" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Extract8) {
            return Ok(expr.clone());
        }
        
        let op1 = if let Some(op) = expr.op1_ref() { op } else { return Ok(expr.clone()); };
        let byte_idx = expr.op2 as u32;
        
        // Extract8 over Zext
        if op1.opkind_is(OpKind::Zext) {
            if let Some(inner) = op1.op1_ref() {
                if let Some(inner_width) = infer_size(inner) {
                    let inner_bytes = (inner_width + 7) / 8;
                    if byte_idx < inner_bytes {
                        // Extract from the original inner expression
                        return Ok(Expr {
                            op1: inner as *const Expr as *mut Expr,
                            op2: byte_idx as *mut Expr,
                            op3: std::ptr::null_mut(),
                            opkind: OpKind::Extract8 as u8,
                            op1_is_const: 0,
                            op2_is_const: 1,
                            op3_is_const: 0,
                        });
                    } else {
                        // Extract from zero-extended part - return 0
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
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 116 }
}

/// Extract over zero-extend clamp rule
pub struct ExtractOverZextClampRule;

impl SimplificationRule for ExtractOverZextClampRule {
    fn name(&self) -> &str { "ExtractOverZextClamp" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Extract) {
            return Ok(expr.clone());
        }
        
        let op1 = if let Some(op) = expr.op1_ref() { op } else { return Ok(expr.clone()); };
        let (high, low) = Expr::unpack_u32_pair_from_ptr(expr.op2);
        
        // Extract over Zext
        if op1.opkind_is(OpKind::Zext) {
            if let Some(inner) = op1.op1_ref() {
                if let Some(inner_width) = infer_size(inner) {
                    if high < inner_width {
                        // Extract entirely within original width
                        let packed = Expr::pack_u32_pair_to_ptr(high, low);
                        return Ok(Expr {
                            op1: inner as *const Expr as *mut Expr,
                            op2: packed,
                            op3: std::ptr::null_mut(),
                            opkind: OpKind::Extract as u8,
                            op1_is_const: 0,
                            op2_is_const: 1,
                            op3_is_const: 0,
                        });
                    } else if low >= inner_width {
                        // Extract entirely from zero-extended part
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
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 117 }
}

/// Extract through concat rule
pub struct ExtractThroughConcatRule;

impl SimplificationRule for ExtractThroughConcatRule {
    fn name(&self) -> &str { "ExtractThroughConcat" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Extract) {
            return Ok(expr.clone());
        }
        
        let concat = if let Some(op) = expr.op1_ref() { op } else { return Ok(expr.clone()); };
        if !concat.opkind_is(OpKind::Concat) {
            return Ok(expr.clone());
        }
        
        let (high, low) = Expr::unpack_u32_pair_from_ptr(expr.op2);
        
        if let (Some(left), Some(right)) = (concat.op1_ref(), concat.op2_ref()) {
            if let (Some(left_width), Some(right_width)) = (infer_size(left), infer_size(right)) {
                let _total_width = left_width + right_width;
                
                if high < right_width {
                    // Extract entirely from right side
                    let packed = Expr::pack_u32_pair_to_ptr(high, low);
                    return Ok(Expr {
                        op1: right as *const Expr as *mut Expr,
                        op2: packed,
                        op3: std::ptr::null_mut(),
                        opkind: OpKind::Extract as u8,
                        op1_is_const: 0,
                        op2_is_const: 1,
                        op3_is_const: 0,
                    });
                } else if low >= right_width {
                    // Extract entirely from left side
                    let new_high = high - right_width;
                    let new_low = low - right_width;
                    let packed = Expr::pack_u32_pair_to_ptr(new_high, new_low);
                    return Ok(Expr {
                        op1: left as *const Expr as *mut Expr,
                        op2: packed,
                        op3: std::ptr::null_mut(),
                        opkind: OpKind::Extract as u8,
                        op1_is_const: 0,
                        op2_is_const: 1,
                        op3_is_const: 0,
                    });
                }
                // Extract spans both sides - more complex handling needed
            }
        }
        
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 125 }
}
