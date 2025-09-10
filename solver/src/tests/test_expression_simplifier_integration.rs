//! Integration tests for expression simplifier with real workloads

use crate::{Expr, OpKind};
use crate::expressions::expression_simplifier::ExpressionSimplifier;

fn create_const_expr(value: u64) -> Expr {
    Expr {
        op1: value as *mut Expr,
        op2: std::ptr::null_mut(),
        op3: std::ptr::null_mut(),
        opkind: OpKind::IsConst as u8,
        op1_is_const: 1,
        op2_is_const: 0,
        op3_is_const: 0,
    }
}

fn create_binary_expr(op: OpKind, left: Expr, right: Expr) -> Expr {
    let left_ptr = Box::into_raw(Box::new(left));
    let right_ptr = Box::into_raw(Box::new(right));
    
    Expr {
        op1: left_ptr,
        op2: right_ptr,
        op3: std::ptr::null_mut(),
        opkind: op as u8,
        op1_is_const: 0,
        op2_is_const: 0,
        op3_is_const: 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arithmetic_identity_simplification() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test X + 0 = X
        let x = create_const_expr(42);
        let zero = create_const_expr(0);
        let add_expr = create_binary_expr(OpKind::Add, x.clone(), zero);
        
        let simplified = simplifier.simplify(&add_expr).expect("Simplification should succeed");
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 42);
    }

    #[test]
    fn test_multiplication_identity_simplification() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test X * 1 = X
        let x = create_const_expr(123);
        let one = create_const_expr(1);
        let mul_expr = create_binary_expr(OpKind::Mul, x.clone(), one);
        
        let simplified = simplifier.simplify(&mul_expr).expect("Simplification should succeed");
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 123);
    }

    #[test]
    fn test_constant_folding_addition() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test constant folding: 5 + 3 = 8
        let five = create_const_expr(5);
        let three = create_const_expr(3);
        let const_add = create_binary_expr(OpKind::Add, five, three);
        
        let simplified = simplifier.simplify(&const_add).expect("Simplification should succeed");
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 8);
    }

    #[test]
    fn test_bitvector_and_zero_simplification() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test X & 0 = 0
        let x = create_const_expr(255);
        let zero = create_const_expr(0);
        let and_expr = create_binary_expr(OpKind::And, x, zero);
        
        let simplified = simplifier.simplify(&and_expr).expect("Simplification should succeed");
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 0);
    }

    #[test]
    fn test_bitvector_or_zero_simplification() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test X | 0 = X
        let x = create_const_expr(42);
        let zero = create_const_expr(0);
        let or_expr = create_binary_expr(OpKind::Or, x.clone(), zero);
        
        let simplified = simplifier.simplify(&or_expr).expect("Simplification should succeed");
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 42);
    }

    #[test]
    fn test_xor_zero_simplification() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test X ^ 0 = X
        let x = create_const_expr(99);
        let zero = create_const_expr(0);
        let xor_expr = create_binary_expr(OpKind::Xor, x.clone(), zero);
        
        let simplified = simplifier.simplify(&xor_expr).expect("Simplification should succeed");
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 99);
    }

    #[test]
    fn test_multiplication_by_zero() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test X * 0 = 0
        let x = create_const_expr(999);
        let zero = create_const_expr(0);
        let mul_expr = create_binary_expr(OpKind::Mul, x, zero);
        
        let simplified = simplifier.simplify(&mul_expr).expect("Simplification should succeed");
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 0);
    }

    #[test]
    fn test_subtraction_by_zero() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test X - 0 = X
        let x = create_const_expr(777);
        let zero = create_const_expr(0);
        let sub_expr = create_binary_expr(OpKind::Sub, x.clone(), zero);
        
        let simplified = simplifier.simplify(&sub_expr).expect("Simplification should succeed");
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 777);
    }

    #[test]
    fn test_safe_structural_equality_integration() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Create two identical expressions: (5 + 3)
        let five1 = create_const_expr(5);
        let three1 = create_const_expr(3);
        let expr1 = create_binary_expr(OpKind::Add, five1, three1);
        
        let five2 = create_const_expr(5);
        let three2 = create_const_expr(3);
        let expr2 = create_binary_expr(OpKind::Add, five2, three2);
        
        // Test (5 + 3) - (5 + 3) should be simplified using SafeStructuralEqualityRule
        let sub_expr = create_binary_expr(OpKind::Sub, expr1, expr2);
        
        let simplified = simplifier.simplify(&sub_expr).expect("Simplification should succeed");
        
        // Should be simplified to 0 by SafeStructuralEqualityRule
        assert!(simplified.opkind_is(OpKind::IsConst));
        assert_eq!(simplified.op1 as u64, 0);
    }

}
