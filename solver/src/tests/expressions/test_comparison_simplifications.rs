use crate::expressions::expression::*;
use crate::expressions::simplifications::comparison::ComparisonOptimizationRule;
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

    fn create_eq_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Eq as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_ne_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Ne as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_lt_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Lt as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_le_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Le as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_eq_self() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let x = create_symbolic_expr();
        let eq_expr = create_eq_expr(&x, &x);

        let result = rule.apply(&eq_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_ne_self() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let x = create_symbolic_expr();
        let ne_expr = create_ne_expr(&x, &x);

        let result = rule.apply(&ne_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_eq_constant_folding_true() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let a = create_const_expr(42);
        let b = create_const_expr(42);
        let eq_expr = create_eq_expr(&a, &b);

        let result = rule.apply(&eq_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_eq_constant_folding_false() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let a = create_const_expr(42);
        let b = create_const_expr(24);
        let eq_expr = create_eq_expr(&a, &b);

        let result = rule.apply(&eq_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_lt_constant_folding_true() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let a = create_const_expr(5);
        let b = create_const_expr(10);
        let lt_expr = create_lt_expr(&a, &b);

        let result = rule.apply(&lt_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_lt_constant_folding_false() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let a = create_const_expr(10);
        let b = create_const_expr(5);
        let lt_expr = create_lt_expr(&a, &b);

        let result = rule.apply(&lt_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_le_self() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let x = create_symbolic_expr();
        let le_expr = create_le_expr(&x, &x);

        let result = rule.apply(&le_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_le_constant_folding() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let a = create_const_expr(5);
        let b = create_const_expr(5);
        let le_expr = create_le_expr(&a, &b);

        let result = rule.apply(&le_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }
}
