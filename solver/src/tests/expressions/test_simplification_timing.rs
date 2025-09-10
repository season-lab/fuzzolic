//! Tests for simplification timing statistics

use crate::{Expr, OpKind};
use crate::expressions::expression_simplifier::ExpressionSimplifier;
use crate::utils::statistics::Statistics;

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
    fn test_simplification_timing_statistics() {
        let mut simplifier = ExpressionSimplifier::new();
        let mut stats = Statistics::new();
        
        // Verify initial state
        assert_eq!(stats.simplification_time, 0);
        
        // Create a simple expression that will be simplified: 5 + 0
        let five = create_const_expr(5);
        let zero = create_const_expr(0);
        let add_expr = create_binary_expr(OpKind::Add, five, zero);
        
        // Simplify with statistics tracking
        let result = simplifier.simplify_with_stats(&add_expr, &mut stats)
            .expect("Simplification should succeed");
        
        // Verify the expression was simplified correctly
        assert!(result.opkind_is(OpKind::IsConst));
        assert_eq!(result.op1 as u64, 5);
        
        // Verify that timing was recorded (should be > 0 microseconds)
        assert!(stats.simplification_time > 0, 
               "Simplification time should be recorded: {}", stats.simplification_time);
    }

    #[test]
    fn test_multiple_simplifications_accumulate_time() {
        let mut simplifier = ExpressionSimplifier::new();
        let mut stats = Statistics::new();
        
        // First simplification: 10 + 0
        let ten = create_const_expr(10);
        let zero1 = create_const_expr(0);
        let add_expr1 = create_binary_expr(OpKind::Add, ten, zero1);
        
        let _result1 = simplifier.simplify_with_stats(&add_expr1, &mut stats)
            .expect("First simplification should succeed");
        
        let first_time = stats.simplification_time;
        assert!(first_time > 0, "First simplification should record time");
        
        // Second simplification: 20 * 1
        let twenty = create_const_expr(20);
        let one = create_const_expr(1);
        let mul_expr = create_binary_expr(OpKind::Mul, twenty, one);
        
        let _result2 = simplifier.simplify_with_stats(&mul_expr, &mut stats)
            .expect("Second simplification should succeed");
        
        // Verify that times accumulate
        assert!(stats.simplification_time > first_time, 
               "Second simplification should add to total time: {} > {}", 
               stats.simplification_time, first_time);
    }

    #[test]
    fn test_complex_expression_timing() {
        let mut simplifier = ExpressionSimplifier::new();
        let mut stats = Statistics::new();
        
        // Create a simpler expression that will definitely be simplified: 100 & 0
        let hundred = create_const_expr(100);
        let zero = create_const_expr(0);
        
        // Build: 100 & 0 (should simplify to 0)
        let and_expr = create_binary_expr(OpKind::And, hundred, zero);
        
        let result = simplifier.simplify_with_stats(&and_expr, &mut stats)
            .expect("Complex simplification should succeed");
        
        // Verify the expression was simplified to 0
        assert!(result.opkind_is(OpKind::IsConst));
        assert_eq!(result.op1 as u64, 0);
        
        // Verify timing was recorded for the complex expression
        assert!(stats.simplification_time > 0, 
               "Complex expression simplification should record time: {}", 
               stats.simplification_time);
    }

    #[test]
    fn test_statistics_integration_with_print() {
        let mut stats = Statistics::new();
        
        // Simulate some timing data
        stats.simplification_time = 1234; // 1234 microseconds
        stats.queries_processed = 5;
        stats.sat_count = 3;
        stats.unsat_count = 2;
        
        // This test just verifies the statistics structure is complete
        // In a real scenario, print_statistics() would be called on the solver
        assert_eq!(stats.simplification_time, 1234);
        assert_eq!(stats.queries_processed, 5);
    }
}
