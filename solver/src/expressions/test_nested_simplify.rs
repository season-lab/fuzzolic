use crate::expressions::expression::{Expr, OpKind};
use crate::expressions::expression_simplifier::ExpressionSimplifier;
use crate::expressions::arena::tls_alloc_opt;

#[cfg(test)]
mod tests {
    use super::*;

    /// Test the nested concat-extract pattern simplification
    #[test]
    fn test_nested_concat_extract_simplification() {
        // Create a base expression: concat(concat(concat(input_3, input_2), input_1), input_0)
        let input_0 = tls_alloc_opt(Expr {
            op1: 0 as *mut Expr, // symbolic input 0
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let input_1 = tls_alloc_opt(Expr {
            op1: 1 as *mut Expr, // symbolic input 1
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let input_2 = tls_alloc_opt(Expr {
            op1: 2 as *mut Expr, // symbolic input 2
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let input_3 = tls_alloc_opt(Expr {
            op1: 3 as *mut Expr, // symbolic input 3
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        // Build: concat(concat(concat(input_3, input_2), input_1), input_0)
        let concat_32 = tls_alloc_opt(Expr {
            op1: input_3,
            op2: input_2,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let concat_21 = tls_alloc_opt(Expr {
            op1: concat_32,
            op2: input_1,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let base_concat = tls_alloc_opt(Expr {
            op1: concat_21,
            op2: input_0,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        // Create extracts: [31:24], [23:16], [15:8], [7:0]
        let extract_31_24 = tls_alloc_opt(Expr {
            op1: base_concat,
            op2: Expr::pack_u32_pair_to_ptr(31, 24),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }).unwrap();

        let extract_23_16 = tls_alloc_opt(Expr {
            op1: base_concat,
            op2: Expr::pack_u32_pair_to_ptr(23, 16),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }).unwrap();

        let extract_15_8 = tls_alloc_opt(Expr {
            op1: base_concat,
            op2: Expr::pack_u32_pair_to_ptr(15, 8),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }).unwrap();

        let extract_7_0 = tls_alloc_opt(Expr {
            op1: base_concat,
            op2: Expr::pack_u32_pair_to_ptr(7, 0),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }).unwrap();

        // Build the nested concat: concat(concat(concat(extract_31_24, extract_23_16), extract_15_8), extract_7_0)
        let nested_concat_1 = tls_alloc_opt(Expr {
            op1: extract_31_24,
            op2: extract_23_16,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let nested_concat_2 = tls_alloc_opt(Expr {
            op1: nested_concat_1,
            op2: extract_15_8,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let nested_concat_final = tls_alloc_opt(Expr {
            op1: nested_concat_2,
            op2: extract_7_0,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        // Test simplification
        let mut simplifier = ExpressionSimplifier::new();
        let simplified = simplifier.simplify(unsafe { &*nested_concat_final }).unwrap();

        println!("Original nested concat structure created");
        println!("Simplified result: opkind = {:?}", simplified.try_opkind());

        // The result should be either the base_concat directly or an Extract(base_concat, 31:0)
        match simplified.try_opkind() {
            Ok(OpKind::Concat) => {
                // Should be simplified to the original base concat
                assert!(std::ptr::eq(&simplified as *const Expr, base_concat), "Should simplify to base concat");
            }
            Ok(OpKind::Extract) => {
                // Should be Extract(base_concat, 31:0)
                assert!(std::ptr::eq(simplified.op1_ref().unwrap() as *const Expr, base_concat), "Extract should be from base concat");
                let (high, low) = Expr::unpack_u32_pair_from_ptr(simplified.op2);
                assert_eq!((high, low), (31, 0), "Should extract full 32-bit range");
            }
            _ => panic!("Unexpected simplification result: {:?}", simplified.try_opkind()),
        }
    }

    /// Test with debug logging enabled
    #[test]
    fn test_debug_nested_simplification() {
        env_logger::init();
        
        // Simple test case that should trigger our rules
        let base = tls_alloc_opt(Expr {
            op1: 42 as *mut Expr, // some symbolic base
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        // Create 4 byte extracts
        let e1 = tls_alloc_opt(Expr {
            op1: base,
            op2: Expr::pack_u32_pair_to_ptr(31, 24),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }).unwrap();

        let e2 = tls_alloc_opt(Expr {
            op1: base,
            op2: Expr::pack_u32_pair_to_ptr(23, 16),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }).unwrap();

        let e3 = tls_alloc_opt(Expr {
            op1: base,
            op2: Expr::pack_u32_pair_to_ptr(15, 8),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }).unwrap();

        let e4 = tls_alloc_opt(Expr {
            op1: base,
            op2: Expr::pack_u32_pair_to_ptr(7, 0),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }).unwrap();

        // Build concat(concat(concat(e1, e2), e3), e4)
        let c1 = tls_alloc_opt(Expr {
            op1: e1,
            op2: e2,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let c2 = tls_alloc_opt(Expr {
            op1: c1,
            op2: e3,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let final_concat = tls_alloc_opt(Expr {
            op1: c2,
            op2: e4,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }).unwrap();

        let mut simplifier = ExpressionSimplifier::new();
        let result = simplifier.simplify(unsafe { &*final_concat }).unwrap();
        
        println!("Simplification completed. Result opkind: {:?}", result.try_opkind());
    }
}
