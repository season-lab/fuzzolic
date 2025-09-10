use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};

/// Trait for expression simplification rules
pub trait SimplificationRule {
    fn name(&self) -> &str;
    fn apply(&self, expr: &Expr) -> Result<Expr>;
    fn priority(&self) -> u32;
}

/// Helper function to get constant value from expression
pub fn get_const(expr: &Expr) -> Option<u64> {
    if expr.is_const_node() {
        Some(expr.op1 as u64)
    } else {
        None
    }
}

/// Helper function to check if expression is zero constant
pub fn is_zero_const(expr: &Expr) -> bool {
    get_const(expr) == Some(0)
}

/// Helper function to infer expression size (simplified version)
pub fn infer_size(expr: &Expr) -> Option<u32> {
    match expr.try_opkind().ok()? {
        OpKind::IsSymbolic => {
            if expr.op2_is_const != 0 {
                Some((expr.op2 as u32) * 8)
            } else {
                Some(8) // Default byte size
            }
        }
        OpKind::IsConst => Some(64), // Constants are 64-bit
        OpKind::Concat => {
            let left_size = expr.safe_op1_ref().and_then(infer_size)?;
            let right_size = expr.safe_op2_ref().and_then(infer_size)?;
            Some(left_size + right_size)
        }
        OpKind::Extract => {
            let (high, low) = Expr::unpack_u32_pair_from_ptr(expr.op2);
            Some(high - low + 1)
        }
        OpKind::Extract8 => Some(8),
        OpKind::Zext => {
            if expr.op2_is_const != 0 {
                Some(expr.op2 as u32)
            } else {
                None
            }
        }
        _ => None,
    }
}

// Re-export all rule modules
pub mod arithmetic;
pub mod bitvector;
pub mod boolean;
pub mod comparison;
pub mod concat_extract;
pub mod constant_folding;
pub mod extract;
pub mod extract_concat_collapse;
pub mod identity;
pub mod structural_equality;
pub mod power_of_two;
pub mod extension_equality;

// Re-export all rules for convenience
pub use arithmetic::*;
pub use bitvector::*;
pub use boolean::*;
pub use comparison::*;
pub use concat_extract::*;
pub use constant_folding::*;
pub use extract::*;
pub use extract_concat_collapse::*;
pub use identity::*;
pub use structural_equality::*;
pub use power_of_two::*;
pub use extension_equality::*;
