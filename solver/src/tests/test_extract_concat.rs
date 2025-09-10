use crate::expressions::expression::*;
use crate::expressions::expression_simplifier::ExpressionSimplifier;
use crate::expressions::simplifications::extract_concat_collapse::ExtractConcatCollapseRule;
use crate::expressions::simplifications::SimplificationRule;

#[cfg(test)]
mod tests {
    use super::*;

#[test]
fn test_extract_concat_collapse() -> anyhow::Result<()> {
    println!("Testing ExtractConcatCollapseRule directly...");
    
    // Create a simple test: Extract8 of a Concat
    // This simulates the pattern we see in Z3: extract(concat(...), range)
    
    // Create mock input expressions
    let input_a = Expr {
        op1: std::ptr::null_mut(),
        op2: 0xAA as *mut Expr, // constant 0xAA
        op3: std::ptr::null_mut(),
        opkind: OpKind::InputSlice as u8,
        op1_is_const: 0,
        op2_is_const: 1,
        op3_is_const: 0,
    };
    
    let input_b = Expr {
        op1: std::ptr::null_mut(),
        op2: 0xBB as *mut Expr, // constant 0xBB
        op3: std::ptr::null_mut(),
        opkind: OpKind::InputSlice as u8,
        op1_is_const: 0,
        op2_is_const: 1,
        op3_is_const: 0,
    };
    
    // Create concat: Concat(input_a, input_b) - input_a is high bits, input_b is low bits
    let concat_ab = Expr {
        op1: &input_a as *const Expr as *mut Expr,
        op2: &input_b as *const Expr as *mut Expr,
        op3: std::ptr::null_mut(),
        opkind: OpKind::Concat as u8,
        op1_is_const: 0,
        op2_is_const: 0,
        op3_is_const: 0,
    };
    
    // Create Extract8 to extract byte 1 (should get input_a since it's the high byte)
    let extract_byte_1 = Expr {
        op1: &concat_ab as *const Expr as *mut Expr,
        op2: 1 as *mut Expr, // byte index 1 (high byte)
        op3: std::ptr::null_mut(),
        opkind: OpKind::Extract8 as u8,
        op1_is_const: 0,
        op2_is_const: 1,
        op3_is_const: 0,
    };
    
    println!("Created Extract8(Concat(input_a, input_b), 1) expression");
    println!("Original expression: opkind={:?}, extracting byte {}", extract_byte_1.opkind, extract_byte_1.op2 as usize);
    
    // Test the rule directly
    let rule = ExtractConcatCollapseRule;
    let result = rule.apply(&extract_byte_1)?;
    
    println!("Rule result: opkind={:?}", result.opkind);
    
    // Also test with full simplifier
    let mut simplifier = ExpressionSimplifier::new();
    let simplified = simplifier.simplify(&extract_byte_1)?;
    
    println!("Full simplifier result: opkind={:?}", simplified.opkind);
    
    // Test Extract8 of byte 0 (should get input_b, the low byte)
    let extract_byte_0 = Expr {
        op1: &concat_ab as *const Expr as *mut Expr,
        op2: 0 as *mut Expr, // byte index 0 (low byte)
        op3: std::ptr::null_mut(),
        opkind: OpKind::Extract8 as u8,
        op1_is_const: 0,
        op2_is_const: 1,
        op3_is_const: 0,
    };
    
    println!("\nTesting Extract8(Concat(input_a, input_b), 0) - should get input_b");
    let result_0 = rule.apply(&extract_byte_0)?;
    println!("Rule result for byte 0: opkind={:?}", result_0.opkind);
    
    Ok(())
}

}
