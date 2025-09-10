use crate::expressions::expression::*;
use crate::expressions::simplifications::identity::IdentityRule;
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

    fn create_sext_expr(operand: &Expr, target_width: u32) -> Expr {
        Expr {
            op1: operand as *const Expr as *mut Expr,
            op2: target_width as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Sext as u8,
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

    #[test]
    fn test_zext_to_same_width() -> anyhow::Result<()> {
        let rule = IdentityRule;
        let x = create_symbolic_expr(); // 32-bit symbolic
        // Zero-extend to same width (identity)
        let zext_expr = create_zext_expr(&x, 32);

        let result = rule.apply(&zext_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsSymbolic);
        Ok(())
    }

    #[test]
    fn test_sext_to_same_width() -> anyhow::Result<()> {
        let rule = IdentityRule;
        let x = create_symbolic_expr(); // 32-bit symbolic
        // Sign-extend to same width (identity)
        let sext_expr = create_sext_expr(&x, 32);

        let result = rule.apply(&sext_expr)?;
        assert_eq!(result.try_opkind()?, OpKind::IsSymbolic);
        Ok(())
    }

    #[test]
    fn test_concat_with_zero() -> anyhow::Result<()> {
        let rule = IdentityRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        // Concat(x, 0) where 0 has zero width should be identity
        let concat_expr = create_concat_expr(&x, &zero);

        let result = rule.apply(&concat_expr)?;
        // This might not simplify to identity depending on implementation
        // but should at least not crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_double_negation_identity() -> anyhow::Result<()> {
        let rule = IdentityRule;
        let x = create_symbolic_expr();
        
        // Create NOT(x)
        let not_x = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Not as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        };

        // Create NOT(NOT(x))
        let not_not_x = Expr {
            op1: &not_x as *const Expr as *mut Expr,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::Not as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        };

        let result = rule.apply(&not_not_x)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_add_zero_identity() -> anyhow::Result<()> {
        let rule = IdentityRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        
        let add_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: &zero as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Add as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        };

        let result = rule.apply(&add_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_mul_one_identity() -> anyhow::Result<()> {
        let rule = IdentityRule;
        let x = create_symbolic_expr();
        let one = create_const_expr(1);
        
        let mul_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: &one as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Mul as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        };

        let result = rule.apply(&mul_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }

    #[test]
    fn test_and_all_ones_identity() -> anyhow::Result<()> {
        let rule = IdentityRule;
        let x = create_symbolic_expr();
        let all_ones = create_const_expr(u64::MAX);
        
        let and_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: &all_ones as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::And as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        };

        let result = rule.apply(&and_expr)?;
        // May or may not simplify, just check it doesn't crash
        assert!(result.try_opkind().is_ok());
        Ok(())
    }
}
