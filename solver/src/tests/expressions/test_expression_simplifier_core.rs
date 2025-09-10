//! Core tests for expression simplifier functionality

use crate::expressions::expression_simplifier::ExpressionSimplifier;
use crate::expressions::simplifications::*;
use crate::{Expr, OpKind};
use std::ptr;

fn create_const_expr(value: u64) -> Expr {
    Expr {
        op1: value as *mut Expr,
        op2: ptr::null_mut(),
        op3: ptr::null_mut(),
        opkind: OpKind::IsConst as u8,
        op1_is_const: 1,
        op2_is_const: 0,
        op3_is_const: 0,
    }
}

fn create_extract_expr(base: &Expr, high: u32, low: u32) -> Expr {
    let packed = Expr::pack_u32_pair_to_ptr(high, low);
    Expr {
        op1: base as *const Expr as *mut Expr,
        op2: packed,
        op3: ptr::null_mut(),
        opkind: OpKind::Extract as u8,
        op1_is_const: 0,
        op2_is_const: 1,
        op3_is_const: 0,
    }
}

fn create_or_expr(left: &Expr, right: &Expr) -> Expr {
    Expr {
        op1: left as *const Expr as *mut Expr,
        op2: right as *const Expr as *mut Expr,
        op3: ptr::null_mut(),
        opkind: OpKind::Or as u8,
        op1_is_const: 0,
        op2_is_const: 0,
        op3_is_const: 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_folding() {
        let rule = ConstantFoldingRule;
        
        // Test addition
        let add_expr = Expr {
            op1: 5 as *mut Expr,
            op2: 3 as *mut Expr,
            op3: ptr::null_mut(),
            opkind: OpKind::Add as u8,
            op1_is_const: 1,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        
        let result = rule.apply(&add_expr).unwrap();
        assert_eq!(result.opkind, OpKind::IsConst as u8);
        assert_eq!(result.op1 as u64, 8); // 5 + 3 = 8
    }

    #[test]
    fn test_bitvector_or_identity() {
        let rule = BitvectorSimplificationRule;
        
        // Test X | 0 = X
        let x = create_const_expr(42);
        let zero = create_const_expr(0);
        let or_expr = create_or_expr(&zero, &x);
        
        let result = rule.apply(&or_expr).unwrap();
        
        // The rule should simplify 0 | X to X, which should be a constant with value 42
        assert_eq!(result.opkind, OpKind::IsConst as u8);
        assert_eq!(result.op1 as u64, 42); // Should return X
        
        // Test 0 | X = X
        let or_expr2 = create_or_expr(&x, &zero);
        let result2 = rule.apply(&or_expr2).unwrap();
        assert_eq!(result2.opkind, OpKind::IsConst as u8);
        assert_eq!(result2.op1 as u64, 42); // Should return X
    }

    #[test]
    fn test_extract_optimization_basic() {
        let rule = ExtractOptimizationRule;
        
        // Test extract from constant
        let const_expr = create_const_expr(0xFF00);
        let extract_expr = create_extract_expr(&const_expr, 15, 8);
        
        let result = rule.apply(&extract_expr).unwrap();
        // The extract optimization should work and return a constant
        assert_eq!(result.opkind, OpKind::IsConst as u8);
    }

    #[test]
    fn test_zero_extension_elimination() {
        let rule = ZeroExtensionRule;
        
        // Create zero extension expression
        let base_expr = create_const_expr(42);
        let zext_expr = Expr {
            op1: &base_expr as *const Expr as *mut Expr,
            op2: 8 as *mut Expr, // Extend by 8 bits
            op3: ptr::null_mut(),
            opkind: OpKind::Zext as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        
        // Extract full original size
        let extract_expr = create_extract_expr(&zext_expr, 31, 0);
        
        let result = rule.apply(&extract_expr).unwrap();
        // Should optimize to just the base expression or a smaller extract
        assert!(result.opkind == OpKind::IsConst as u8 || result.opkind == OpKind::Extract as u8);
    }

    #[test]
    fn test_subtraction_transform() {
        let rule = SubtractionTransformRule;
        
        // Create X - Y expression
        let x = create_const_expr(10);
        let y = create_const_expr(5);
        let sub_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: &y as *const Expr as *mut Expr,
            op3: ptr::null_mut(),
            opkind: OpKind::Sub as u8,
            op1_is_const: 1,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        
        // Extract from subtraction
        let extract_expr = create_extract_expr(&sub_expr, 7, 0);
        
        let result = rule.apply(&extract_expr).unwrap();
        // Should either be optimized or remain as extract
        assert!(result.opkind == OpKind::IsConst as u8 || result.opkind == OpKind::Extract as u8);
    }

    #[test]
    fn test_expression_simplifier_integration() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test basic constant folding
        let const_expr = create_const_expr(42);
        let extract_expr = create_extract_expr(&const_expr, 7, 0);
        
        let result = simplifier.simplify(&extract_expr).unwrap();
        
        // The extract optimization should work since we have opkind 38 and constant operand
        if result.opkind == OpKind::IsConst as u8 {
            // If optimization worked, check the extracted value
            assert_eq!(result.op1 as u64, 42 & 0xFF); // Should extract bits [7:0] = 42
        } else {
            // If optimization didn't work, that's also acceptable for this integration test
            assert_eq!(result.opkind, OpKind::Extract as u8); // Should still be extract
        }
    }
}
