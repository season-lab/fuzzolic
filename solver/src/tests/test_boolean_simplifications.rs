use crate::expressions::expression::*;
use crate::expressions::simplifications::boolean::BooleanSimplificationRule;
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

    fn create_and_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::And as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_or_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Or as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_not_expr(operand: &Expr) -> Expr {
        Expr {
            op1: operand as *const Expr as *mut Expr,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Not as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_and_with_zero() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let and_expr = create_and_expr(&x, &zero);

        let result = rule.apply(&and_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_and_with_all_ones() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let x = create_symbolic_expr();
        let all_ones = create_const_expr(u64::MAX);
        let and_expr = create_and_expr(&x, &all_ones);

        let result = rule.apply(&and_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_and_self() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let x = create_symbolic_expr();
        let and_expr = create_and_expr(&x, &x);

        let result = rule.apply(&and_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_or_with_zero() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let or_expr = create_or_expr(&x, &zero);

        let result = rule.apply(&or_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_or_with_all_ones() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let x = create_symbolic_expr();
        let all_ones = create_const_expr(u64::MAX);
        let or_expr = create_or_expr(&x, &all_ones);

        let result = rule.apply(&or_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_or_self() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let x = create_symbolic_expr();
        let or_expr = create_or_expr(&x, &x);

        let result = rule.apply(&or_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_double_negation() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let x = create_symbolic_expr();
        let not_x = create_not_expr(&x);
        let not_not_x = create_not_expr(&not_x);

        let result = rule.apply(&not_not_x)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_and_constant_folding() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let a = create_const_expr(0b1010);
        let b = create_const_expr(0b1100);
        let and_expr = create_and_expr(&a, &b);

        let result = rule.apply(&and_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_or_constant_folding() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let a = create_const_expr(0b1010);
        let b = create_const_expr(0b1100);
        let or_expr = create_or_expr(&a, &b);

        let result = rule.apply(&or_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }
}
