use crate::expressions::expression::*;
use crate::expressions::simplifications::arithmetic::ArithmeticSimplificationRule;
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
            op2: 4 as *mut Expr, // 4 bytes
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    fn create_add_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Add as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_sub_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Sub as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_mul_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Mul as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_add_zero_left() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let zero = create_const_expr(0);
        let x = create_symbolic_expr();
        let add_expr = create_add_expr(&zero, &x);

        let result = rule.apply(&add_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsSymbolic);
        Ok(())
    }

    #[test]
    fn test_add_zero_right() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let add_expr = create_add_expr(&x, &zero);

        let result = rule.apply(&add_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsSymbolic);
        Ok(())
    }

    #[test]
    fn test_add_constant_folding() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let a = create_const_expr(5);
        let b = create_const_expr(3);
        let add_expr = create_add_expr(&a, &b);

        let result = rule.apply(&add_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 8);
        Ok(())
    }

    #[test]
    fn test_sub_zero() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let sub_expr = create_sub_expr(&x, &zero);

        let result = rule.apply(&sub_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsSymbolic);
        Ok(())
    }

    #[test]
    fn test_sub_self() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let x = create_symbolic_expr();
        let sub_expr = create_sub_expr(&x, &x);

        let result = rule.apply(&sub_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 0);
        Ok(())
    }

    #[test]
    fn test_mul_zero() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let mul_expr = create_mul_expr(&x, &zero);

        let result = rule.apply(&mul_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 0);
        Ok(())
    }

    #[test]
    fn test_mul_one() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let x = create_symbolic_expr();
        let one = create_const_expr(1);
        let mul_expr = create_mul_expr(&x, &one);

        let result = rule.apply(&mul_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsSymbolic);
        Ok(())
    }

    #[test]
    fn test_mul_constant_folding() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let a = create_const_expr(6);
        let b = create_const_expr(7);
        let mul_expr = create_mul_expr(&a, &b);

        let result = rule.apply(&mul_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 42);
        Ok(())
    }
}
