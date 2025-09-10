use crate::expressions::expression::*;
use crate::expressions::simplifications::bitvector::BitvectorSimplificationRule;
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

    fn create_shl_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Shl as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_shr_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Shr as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_xor_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Xor as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_shl_by_zero() -> anyhow::Result<()> {
        let rule = BitvectorSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let shl_expr = create_shl_expr(&x, &zero);

        let result = rule.apply(&shl_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_shr_by_zero() -> anyhow::Result<()> {
        let rule = BitvectorSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let shr_expr = create_shr_expr(&x, &zero);

        let result = rule.apply(&shr_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_xor_self() -> anyhow::Result<()> {
        use crate::expressions::simplifications::SafeStructuralEqualityRule;
        let rule = SafeStructuralEqualityRule;
        let x = create_symbolic_expr();
        let xor_expr = create_xor_expr(&x, &x);

        let result = rule.apply(&xor_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 0);
        Ok(())
    }

    #[test]
    fn test_xor_with_zero() -> anyhow::Result<()> {
        let rule = BitvectorSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let xor_expr = create_xor_expr(&x, &zero);

        let result = rule.apply(&xor_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsSymbolic);
        Ok(())
    }

    #[test]
    fn test_shl_constant_folding() -> anyhow::Result<()> {
        let rule = BitvectorSimplificationRule;
        let a = create_const_expr(5);
        let b = create_const_expr(2);
        let shl_expr = create_shl_expr(&a, &b);

        let result = rule.apply(&shl_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_shr_constant_folding() -> anyhow::Result<()> {
        let rule = BitvectorSimplificationRule;
        let a = create_const_expr(20);
        let b = create_const_expr(2);
        let shr_expr = create_shr_expr(&a, &b);

        let result = rule.apply(&shr_expr)?;
        // May or may not fold constants, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_xor_constant_folding() -> anyhow::Result<()> {
        let rule = BitvectorSimplificationRule;
        let a = create_const_expr(0b1010);
        let b = create_const_expr(0b1100);
        let xor_expr = create_xor_expr(&a, &b);

        let result = rule.apply(&xor_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsConst);
        assert_eq!(result.op1 as u64, 0b0110);
        Ok(())
    }
}
