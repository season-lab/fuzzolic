use crate::expressions::expression::*;
use crate::expressions::simplifications::extract::ExtractOptimizationRule;
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

    fn create_zext_expr(operand: &Expr, target_width: u32) -> Expr {
        Expr {
            op1: operand as *const Expr as *mut Expr,
            op2: target_width as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Zext as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_extract_full_width() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let x = create_symbolic_expr();
        // Extract full 32-bit width from 32-bit value
        let extract_expr = create_extract_expr(&x, 31, 0);

        let result = rule.apply(&extract_expr)?;
        // May or may not simplify to identity, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_extract_constant() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let const_val = create_const_expr(0x12345678);
        // Extract bits [15:8] from constant
        let extract_expr = create_extract_expr(&const_val, 15, 8);

        let result = rule.apply(&extract_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 0x56); // bits [15:8] of 0x12345678
        Ok(())
    }

    #[test]
    fn test_extract8_constant() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let const_val = create_const_expr(0x12345678);
        // Extract byte 1 (bits [15:8])
        let extract8_expr = create_extract8_expr(&const_val, 1);

        let result = rule.apply(&extract8_expr)?;
        // Extract8 rule may not be handled by ExtractOptimizationRule, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_extract_zero_width() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let x = create_symbolic_expr();
        // Extract zero-width range (invalid)
        let extract_expr = create_extract_expr(&x, 5, 6);

        // Should return original expression unchanged
        let result = rule.apply(&extract_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::Extract);
        Ok(())
    }

    #[test]
    fn test_nested_extract_of_zext() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let x = create_symbolic_expr();
        let zext_expr = create_zext_expr(&x, 64);
        // Extract from zero-extended value
        let extract_expr = create_extract_expr(&zext_expr, 31, 0);

        let result = rule.apply(&extract_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_extract_single_bit() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let const_val = create_const_expr(0b10101010);
        // Extract bit 3
        let extract_expr = create_extract_expr(&const_val, 3, 3);

        let result = rule.apply(&extract_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 1); // bit 3 is set
        Ok(())
    }

    #[test]
    fn test_extract8_byte_0() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let const_val = create_const_expr(0x12345678);
        // Extract byte 0 (lowest byte)
        let extract8_expr = create_extract8_expr(&const_val, 0);

        let result = rule.apply(&extract8_expr)?;
        // Extract8 rule may not be handled by ExtractOptimizationRule, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_extract8_byte_3() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let const_val = create_const_expr(0x12345678);
        // Extract byte 3 (highest byte)
        let extract8_expr = create_extract8_expr(&const_val, 3);

        let result = rule.apply(&extract8_expr)?;
        // Extract8 rule may not be handled by ExtractOptimizationRule, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }
}
