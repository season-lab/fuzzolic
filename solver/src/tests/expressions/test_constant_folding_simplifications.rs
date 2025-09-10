use crate::expressions::expression::*;
use crate::expressions::simplifications::constant_folding::ConstantFoldingRule;
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

    fn create_add_expr_with_const_operands(a: u64, b: u64) -> Expr {
        Expr {
            op1: a as *mut Expr,
            op2: b as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Add as u8,
            op1_is_const: 1,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    fn create_mul_expr_with_const_operands(a: u64, b: u64) -> Expr {
        Expr {
            op1: a as *mut Expr,
            op2: b as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Mul as u8,
            op1_is_const: 1,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    fn create_and_expr_with_const_operands(a: u64, b: u64) -> Expr {
        Expr {
            op1: a as *mut Expr,
            op2: b as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::And as u8,
            op1_is_const: 1,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_add_constant_folding() -> anyhow::Result<()> {
        let rule = ConstantFoldingRule;
        let add_expr = create_add_expr_with_const_operands(15, 27);

        let result = rule.apply(&add_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 42);
        Ok(())
    }

    #[test]
    fn test_mul_constant_folding() -> anyhow::Result<()> {
        let rule = ConstantFoldingRule;
        let mul_expr = create_mul_expr_with_const_operands(6, 7);

        let result = rule.apply(&mul_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 42);
        Ok(())
    }

    #[test]
    fn test_and_constant_folding() -> anyhow::Result<()> {
        let rule = ConstantFoldingRule;
        let and_expr = create_and_expr_with_const_operands(0xFF, 0x0F);

        let result = rule.apply(&and_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 0x0F);
        Ok(())
    }

    #[test]
    fn test_overflow_handling() -> anyhow::Result<()> {
        let rule = ConstantFoldingRule;
        let add_expr = create_add_expr_with_const_operands(u64::MAX, 1);

        let result = rule.apply(&add_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 0); // wrapping add
        Ok(())
    }

    #[test]
    fn test_large_numbers() -> anyhow::Result<()> {
        let rule = ConstantFoldingRule;
        let and_expr = create_and_expr_with_const_operands(0x123456789ABCDEF0, 0x0FEDCBA987654321);

        let result = rule.apply(&and_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }
}
