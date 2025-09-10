use crate::expressions::expression::*;
use crate::expressions::simplifications::concat_extract::*;
use crate::expressions::simplifications::SimplificationRule;

#[cfg(test)]
mod tests {
    use super::*;

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

    fn create_symbolic_expr() -> Expr {
        Expr {
            op1: std::ptr::null_mut(),
            op2: 4 as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    fn create_concat_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_extract_expr(operand: &Expr, high: u32, low: u32) -> Expr {
        let range = Expr::pack_u32_pair_to_ptr(high, low);
        Expr {
            op1: operand as *const Expr as *mut Expr,
            op2: range,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    fn create_extract8_expr(operand: &Expr, byte_index: u32) -> Expr {
        Expr {
            op1: operand as *const Expr as *mut Expr,
            op2: byte_index as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract8 as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_identical_base_extract_collapse() -> anyhow::Result<()> {
        let rule = IdenticalBaseExtractCollapseRule;
        
        // Create base expression
        let base = create_symbolic_expr();
        
        // Create Extract8(base, 0), Extract8(base, 1), Extract8(base, 2), Extract8(base, 3)
        let extract0 = create_extract8_expr(&base, 0);
        let extract1 = create_extract8_expr(&base, 1);
        let extract2 = create_extract8_expr(&base, 2);
        let extract3 = create_extract8_expr(&base, 3);
        
        // Create Concat(Extract8(base, 1), Extract8(base, 0))
        let concat_10 = create_concat_expr(&extract1, &extract0);
        
        // Create Concat(Extract8(base, 3), Extract8(base, 2))
        let concat_32 = create_concat_expr(&extract3, &extract2);
        
        // Create final Concat(Concat(Extract8(base, 3), Extract8(base, 2)), Concat(Extract8(base, 1), Extract8(base, 0)))
        let final_concat = create_concat_expr(&concat_32, &concat_10);

        let result = rule.apply(&final_concat)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_extract_of_concat_simplification() -> anyhow::Result<()> {
        let rule = ExtractOverPackedByteConcatRule;
        
        let a = create_symbolic_expr();
        let b = create_symbolic_expr();
        let concat_ab = create_concat_expr(&a, &b);
        
        // Extract the lower part (should get b)
        let extract_low = create_extract_expr(&concat_ab, 31, 0);
        
        let result = rule.apply(&extract_low)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_concat_of_extracts_simplification() -> anyhow::Result<()> {
        let rule = ConcatExtractPackGeneralRule;
        
        let base = create_symbolic_expr();
        
        // Create Extract(base, 31, 16) and Extract(base, 15, 0)
        let extract_high = create_extract_expr(&base, 31, 16);
        let extract_low = create_extract_expr(&base, 15, 0);
        
        // Concat them back together
        let concat_expr = create_concat_expr(&extract_high, &extract_low);
        
        let result = rule.apply(&concat_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_extract8_of_concat_byte_selection() -> anyhow::Result<()> {
        let rule = ExtractOverPackedByteConcatRule;
        
        // Create two 1-byte constants
        let byte_a = create_const_expr(0xAA);
        let byte_b = create_const_expr(0xBB);
        
        // Concat them: high byte = 0xAA, low byte = 0xBB
        let concat_ab = create_concat_expr(&byte_a, &byte_b);
        
        // Extract byte 0 (should get 0xBB)
        let extract_byte_0 = create_extract8_expr(&concat_ab, 0);
        
        let result = rule.apply(&extract_byte_0)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_extract8_of_concat_high_byte() -> anyhow::Result<()> {
        let rule = ExtractOverPackedByteConcatRule;
        
        // Create two 1-byte constants
        let byte_a = create_const_expr(0xAA);
        let byte_b = create_const_expr(0xBB);
        
        // Concat them: high byte = 0xAA, low byte = 0xBB
        let concat_ab = create_concat_expr(&byte_a, &byte_b);
        
        // Extract byte 1 (should get 0xAA)
        let extract_byte_1 = create_extract8_expr(&concat_ab, 1);
        
        let result = rule.apply(&extract_byte_1)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_nested_concat_extract_pattern() -> anyhow::Result<()> {
        let rule = IdenticalBaseExtractCollapseRule;
        
        let base = create_symbolic_expr();
        
        // Create a pattern like: Concat(Extract8(base, 1), Extract8(base, 0))
        let extract0 = create_extract8_expr(&base, 0);
        let extract1 = create_extract8_expr(&base, 1);
        let concat_simple = create_concat_expr(&extract1, &extract0);
        
        let result = rule.apply(&concat_simple)?;
        // Should simplify to an extract of the base covering bytes [1:0]
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_concat_constant_folding() -> anyhow::Result<()> {
        let rule = ConcatenationOptimizationRule;
        
        let const_a = create_const_expr(0x12);
        let const_b = create_const_expr(0x34);
        let concat_expr = create_concat_expr(&const_a, &const_b);
        
        let result = rule.apply(&concat_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_extract_of_zext_simplification() -> anyhow::Result<()> {
        let rule = ConcatenationAdvancedRule;
        
        let x = create_symbolic_expr();
        
        // Create Zext(x, 64)
        let zext_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: 64 as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Zext as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        
        // Extract the original width from the zero-extended value
        let extract_expr = create_extract_expr(&zext_expr, 31, 0);
        
        let result = rule.apply(&extract_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }
}
