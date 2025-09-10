//! Tests for concrete evaluation functionality

use crate::solver::concrete_eval::{ConcreteEvaluator, BinaryOp};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_operations() {
        let evaluator = ConcreteEvaluator::new();
        
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Add, 5, 3).unwrap(), 8);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Sub, 5, 3).unwrap(), 2);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Mul, 5, 3).unwrap(), 15);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Div, 15, 3).unwrap(), 5);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::And, 0b1010, 0b1100).unwrap(), 0b1000);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Or, 0b1010, 0b1100).unwrap(), 0b1110);
    }

    #[test]
    fn test_extract() {
        let evaluator = ConcreteEvaluator::new();
        
        // Extract bits [7:4] from 0xFF (should be 0xF)
        assert_eq!(evaluator.eval_extract(0xFF, 7, 4).unwrap(), 0xF);
        
        // Extract bits [3:0] from 0xFF (should be 0xF)
        assert_eq!(evaluator.eval_extract(0xFF, 3, 0).unwrap(), 0xF);
    }
}
