use crate::expressions::expression::*;
use crate::expressions::simplifications::*;
use crate::expressions::expression_simplifier::ExpressionSimplifier;

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

    fn create_binary_expr(left: &Expr, right: &Expr, opkind: OpKind) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: opkind as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_arithmetic_rules_dont_crash() -> anyhow::Result<()> {
        let rule = ArithmeticSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let one = create_const_expr(1);
        let five = create_const_expr(5);

        // Test various arithmetic expressions
        let add_expr = create_binary_expr(&x, &zero, OpKind::Add);
        let result = rule.apply(&add_expr)?;
        assert!(result.try_opkind().is_ok());

        let mul_expr = create_binary_expr(&five, &one, OpKind::Mul);
        let result = rule.apply(&mul_expr)?;
        assert!(result.try_opkind().is_ok());

        let sub_expr = create_binary_expr(&x, &x, OpKind::Sub);
        let result = rule.apply(&sub_expr)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_boolean_rules_dont_crash() -> anyhow::Result<()> {
        let rule = BooleanSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let all_ones = create_const_expr(u64::MAX);

        let and_expr = create_binary_expr(&x, &zero, OpKind::And);
        let result = rule.apply(&and_expr)?;
        assert!(result.try_opkind().is_ok());

        let or_expr = create_binary_expr(&x, &all_ones, OpKind::Or);
        let result = rule.apply(&or_expr)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_bitvector_rules_dont_crash() -> anyhow::Result<()> {
        let rule = BitvectorSimplificationRule;
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);
        let two = create_const_expr(2);

        let shl_expr = create_binary_expr(&x, &zero, OpKind::Shl);
        let result = rule.apply(&shl_expr)?;
        assert!(result.try_opkind().is_ok());

        let xor_expr = create_binary_expr(&x, &x, OpKind::Xor);
        let result = rule.apply(&xor_expr)?;
        assert!(result.try_opkind().is_ok());

        let shr_expr = create_binary_expr(&two, &zero, OpKind::Shr);
        let result = rule.apply(&shr_expr)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_comparison_rules_dont_crash() -> anyhow::Result<()> {
        let rule = ComparisonOptimizationRule;
        let x = create_symbolic_expr();
        let five = create_const_expr(5);
        let ten = create_const_expr(10);

        let eq_expr = create_binary_expr(&x, &x, OpKind::Eq);
        let result = rule.apply(&eq_expr)?;
        assert!(result.try_opkind().is_ok());

        let ne_expr = create_binary_expr(&five, &ten, OpKind::Ne);
        let result = rule.apply(&ne_expr)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_constant_folding_rules_dont_crash() -> anyhow::Result<()> {
        let rule = ConstantFoldingRule;
        let five = create_const_expr(5);
        let three = create_const_expr(3);

        let add_expr = create_binary_expr(&five, &three, OpKind::Add);
        let result = rule.apply(&add_expr)?;
        assert!(result.try_opkind().is_ok());

        let mul_expr = create_binary_expr(&five, &three, OpKind::Mul);
        let result = rule.apply(&mul_expr)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_extract_rules_dont_crash() -> anyhow::Result<()> {
        let rule = ExtractOptimizationRule;
        let x = create_symbolic_expr();
        let const_val = create_const_expr(0x12345678);

        // Test Extract
        let range = Expr::pack_u32_pair_to_ptr(15, 8);
        let extract_expr = Expr {
            op1: &const_val as *const Expr as *mut Expr,
            op2: range,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        let result = rule.apply(&extract_expr)?;
        assert!(result.try_opkind().is_ok());

        // Test Extract8
        let extract8_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: 1 as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Extract8 as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        let result = rule.apply(&extract8_expr)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_identity_rules_dont_crash() -> anyhow::Result<()> {
        let rule = IdentityRule;
        let x = create_symbolic_expr();

        // Test Zext
        let zext_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: 64 as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Zext as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        let result = rule.apply(&zext_expr)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_concat_extract_rules_dont_crash() -> anyhow::Result<()> {
        let rule = IdenticalBaseExtractCollapseRule;
        let x = create_symbolic_expr();
        let y = create_symbolic_expr();

        let concat_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: &y as *const Expr as *mut Expr,
            op3: std::ptr::null_mut(),
            opkind: OpKind::Concat as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        };
        let result = rule.apply(&concat_expr)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_expression_simplifier_integration() -> anyhow::Result<()> {
        let mut simplifier = ExpressionSimplifier::new();
        let x = create_symbolic_expr();
        let zero = create_const_expr(0);

        // Test that simplifier can handle various expressions without crashing
        let add_expr = create_binary_expr(&x, &zero, OpKind::Add);
        let result = simplifier.simplify(&add_expr)?;
        assert!(result.try_opkind().is_ok());

        let const_a = create_const_expr(5);
        let const_b = create_const_expr(3);
        let const_add = create_binary_expr(&const_a, &const_b, OpKind::Add);
        let result = simplifier.simplify(&const_add)?;
        assert!(result.try_opkind().is_ok());

        Ok(())
    }

    #[test]
    fn test_rule_priorities() {
        // Test that all rules have valid priorities
        assert!(ArithmeticSimplificationRule.priority() > 0);
        assert!(BooleanSimplificationRule.priority() > 0);
        assert!(BitvectorSimplificationRule.priority() > 0);
        assert!(ComparisonOptimizationRule.priority() > 0);
        assert!(ConstantFoldingRule.priority() > 0);
        assert!(ExtractOptimizationRule.priority() > 0);
        assert!(IdentityRule.priority() > 0);
        assert!(IdenticalBaseExtractCollapseRule.priority() > 0);
    }

    #[test]
    fn test_rule_names() {
        // Test that all rules have non-empty names
        assert!(!ArithmeticSimplificationRule.name().is_empty());
        assert!(!BooleanSimplificationRule.name().is_empty());
        assert!(!BitvectorSimplificationRule.name().is_empty());
        assert!(!ComparisonOptimizationRule.name().is_empty());
        assert!(!ConstantFoldingRule.name().is_empty());
        assert!(!ExtractOptimizationRule.name().is_empty());
        assert!(!IdentityRule.name().is_empty());
        assert!(!IdenticalBaseExtractCollapseRule.name().is_empty());
    }
}
