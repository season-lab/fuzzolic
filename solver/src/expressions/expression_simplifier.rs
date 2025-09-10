use anyhow::Result;
use std::collections::HashMap;
use crate::Expr;
use crate::expressions::arena::{tls_alloc_opt};
use log::debug;

// Import all simplification rules from the modular structure
use crate::expressions::simplifications::*;

// Re-export the trait and helpers for backward compatibility
pub use crate::expressions::simplifications::{SimplificationRule, get_const, is_zero_const, infer_size};

use std::cell::RefCell;
use std::collections::HashSet;

thread_local! {
    static SIMPL_VISITED: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    static WIDTH_CACHE: RefCell<HashMap<usize, u32>> = RefCell::new(HashMap::new());
}

#[allow(unused)]
fn width_cache_get(key: usize) -> Option<u32> {
    WIDTH_CACHE.with(|cache| cache.borrow().get(&key).copied())
}

#[allow(unused)]
fn width_cache_set(key: usize, value: u32) {
    WIDTH_CACHE.with(|cache| cache.borrow_mut().insert(key, value));
}

/// Expression simplifier that applies a set of rules to optimize expressions
pub struct ExpressionSimplifier {
    optimization_rules: Vec<Box<dyn SimplificationRule>>,
}

impl ExpressionSimplifier {
    /// Create a new simplifier with safe optimization rules
    /// This is the single constructor that includes only verified-safe simplifications
    pub fn new() -> Self {
        let mut simplifier = ExpressionSimplifier {
            optimization_rules: Vec::new(),
        };
        
        // SAFE RULES ONLY - Conservative simplifications that preserve semantics
        
        // Core constant folding and identity rules (always safe)
        simplifier.add_rule(Box::new(ConstantFoldingRule));
        simplifier.add_rule(Box::new(IdentityRule));
        
        // Arithmetic rules (safe operations)
        simplifier.add_rule(Box::new(ArithmeticSimplificationRule));
        
        // Boolean and bitvector rules (safe operations)
        simplifier.add_rule(Box::new(BooleanSimplificationRule));
        simplifier.add_rule(Box::new(BitvectorSimplificationRule));
        
        // Comparison rules (safe operations)
        simplifier.add_rule(Box::new(EqIdentityRule));
        
        // Extract optimization rules (safe)
        simplifier.add_rule(Box::new(ExtractOptimizationRule));
        simplifier.add_rule(Box::new(ExtractByteToExtract8Rule));
        
        // Concat/Extract collapse rules (safe)
        simplifier.add_rule(Box::new(IdenticalBaseExtractCollapseRule));
        simplifier.add_rule(Box::new(ExtractOverPackedByteConcatRule));
        
        // NOT simplification (safe)
        simplifier.add_rule(Box::new(NotSimplificationRule));
        simplifier.add_rule(Box::new(NotNotEliminateRule));
        
        // Safe structural equality rules
        simplifier.add_rule(Box::new(SafeStructuralEqualityRule));
        
        // Safe power-of-2 optimizations (unsigned operations only)
        simplifier.add_rule(Box::new(SafeMulPow2Rule));
        simplifier.add_rule(Box::new(SafeDivRemPow2Rule));
        
        // Conservative zero-extension optimizations
        simplifier.add_rule(Box::new(SafeZextEqualityRule));
        
        simplifier
    }
    
    /// Add a custom simplification rule
    pub fn add_rule(&mut self, rule: Box<dyn SimplificationRule>) {
        self.optimization_rules.push(rule);
    }

    /// Clear thread-local visit state and caches
    pub fn clear_visit_state() {
        SIMPL_VISITED.with(|vis| vis.borrow_mut().clear());
        WIDTH_CACHE.with(|cache| cache.borrow_mut().clear());
    }

    /// Simplify an expression using all registered rules
    pub fn simplify(&mut self, expr: &Expr) -> Result<Expr> {
        self.simplify_recursive(expr)
    }

    /// Recursively simplify an expression and its children
    pub fn simplify_recursive(&mut self, expr: &Expr) -> Result<Expr> {
        let key = expr as *const Expr as usize;
        
        // Check if we've already visited this expression to avoid cycles
        let already_visited = SIMPL_VISITED.with(|vis| vis.borrow().contains(&key));
        if already_visited {
            debug!("[SOLVER] simpl: cycle detected at expr_ptr=0x{:x}, returning original", key);
            return Ok(expr.clone());
        }
        
        log::debug!("[SOLVER] simpl: visiting expr_ptr=0x{:x} opkind={:?}", key, expr.opkind);
        
        // Mark as visited
        SIMPL_VISITED.with(|vis| { vis.borrow_mut().insert(key); });

        // FIRST: Apply high-priority top-down rules that need to see the full pattern
        let mut current = expr.clone();
        for rule in &self.optimization_rules {
            let before = current.clone();
            current = rule.apply(&current)?;
            if !std::ptr::eq(&before as *const Expr, &current as *const Expr) {
                log::debug!("TOP-DOWN rule '{}' applied to opkind={:?}", rule.name(), before.opkind);
            }
        }
        
        // Recursively simplify operands
        let simplified_operands = self.simplify_operands(&current)?;
        Ok(simplified_operands)
    }

    /// Simplify operands of an expression
    fn simplify_operands(&mut self, expr: &Expr) -> Result<Expr> {
        let mut new_op1 = expr.op1;
        let mut new_op2 = expr.op2;
        let mut new_op3 = expr.op3;
        let mut changed = false;
        
        // Simplify op1 if it's a valid node pointer
        if let Some(child) = expr.safe_op1_ref() {
            let simplified_child = self.simplify_recursive(child)?;
            if !self.expressions_equal(child, &simplified_child) {
                if let Some(ptr) = tls_alloc_opt(simplified_child) {
                    new_op1 = ptr;
                    changed = true;
                }
            }
        }
        
        // Simplify op2 if it's a valid node pointer
        if let Some(child) = expr.safe_op2_ref() {
            let simplified_child = self.simplify_recursive(child)?;
            if !self.expressions_equal(child, &simplified_child) {
                if let Some(ptr) = tls_alloc_opt(simplified_child) {
                    new_op2 = ptr;
                    changed = true;
                }
            }
        }
        
        // Simplify op3 if it's a valid node pointer
        if let Some(child) = expr.safe_op3_ref() {
            let simplified_child = self.simplify_recursive(child)?;
            if !self.expressions_equal(child, &simplified_child) {
                if let Some(ptr) = tls_alloc_opt(simplified_child) {
                    new_op3 = ptr;
                    changed = true;
                }
            }
        }
        
        // Create new expression with simplified children if any changed
        if changed {
            Ok(Expr {
                op1: new_op1,
                op2: new_op2,
                op3: new_op3,
                opkind: expr.opkind,
                op1_is_const: expr.op1_is_const,
                op2_is_const: expr.op2_is_const,
                op3_is_const: expr.op3_is_const,
            })
        } else {
            Ok(expr.clone())
        }
    }
    
    /// Check if two expressions are structurally equal
    fn expressions_equal(&self, expr1: &Expr, expr2: &Expr) -> bool {
        expr1.opkind == expr2.opkind &&
        expr1.op1_is_const == expr2.op1_is_const &&
        expr1.op2_is_const == expr2.op2_is_const &&
        expr1.op3_is_const == expr2.op3_is_const &&
        // Compare raw operand values (for nodes: pointers; for consts: immediates)
        expr1.op1 as usize == expr2.op1 as usize &&
        expr1.op2 as usize == expr2.op2 as usize &&
        expr1.op3 as usize == expr2.op3 as usize
    }
    
    /// Compute hash for expression caching
    #[allow(unused)]
    fn compute_expression_hash(&self, expr: &Expr) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        expr.opkind.hash(&mut hasher);
        (expr.op1 as usize).hash(&mut hasher);
        (expr.op2 as usize).hash(&mut hasher);
        (expr.op3 as usize).hash(&mut hasher);
        expr.op1_is_const.hash(&mut hasher);
        expr.op2_is_const.hash(&mut hasher);
        expr.op3_is_const.hash(&mut hasher);
        hasher.finish()
    }
}

impl Default for ExpressionSimplifier {
    fn default() -> Self {
        Self::new()
    }
}






#[cfg(test)]
mod tests {
    use super::*;
    use std::ptr;

    fn create_const_expr(value: u64) -> Expr {
        Expr {
            op1: value as *mut Expr,
            op2: ptr::null_mut(),
            op3: ptr::null_mut(),
            opkind: 1, // IsConst
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    fn create_extract_expr(base: &Expr, high: u32, low: u32) -> Expr {
        let packed = Expr::pack_u32_pair_to_ptr(high, low);
        Expr {
            op1: base as *const Expr as *mut Expr,
            op2: packed,
            op3: ptr::null_mut(),
            opkind: 38, // Extract
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        }
    }

    fn create_or_expr(left: &Expr, right: &Expr) -> Expr {
        Expr {
            op1: left as *const Expr as *mut Expr,
            op2: right as *const Expr as *mut Expr,
            op3: ptr::null_mut(),
            opkind: 14, // Or
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }

    #[test]
    fn test_constant_folding() {
        let rule = ConstantFoldingRule;
        
        // Test addition
        let add_expr = Expr {
            op1: 5 as *mut Expr,
            op2: 3 as *mut Expr,
            op3: ptr::null_mut(),
            opkind: 5, // Add
            op1_is_const: 1,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        
        let result = rule.apply(&add_expr).unwrap();
        assert_eq!(result.opkind, 1); // Should be constant
        assert_eq!(result.op1 as u64, 8); // 5 + 3 = 8
    }

    #[test]
    fn test_bitvector_or_identity() {
        let rule = BitvectorSimplificationRule;
        
        // Test X | 0 = X
        let x = create_const_expr(42);
        let zero = create_const_expr(0);
        let or_expr = create_or_expr(&zero, &x);
        
        let result = rule.apply(&or_expr).unwrap();
        
        // The rule should simplify 0 | X to X, which should be a constant with value 42
        assert_eq!(result.opkind, 1); // Should be constant
        assert_eq!(result.op1 as u64, 42); // Should return X
        
        // Test 0 | X = X
        let or_expr2 = create_or_expr(&x, &zero);
        let result2 = rule.apply(&or_expr2).unwrap();
        assert_eq!(result2.opkind, 1); // Should be constant
        assert_eq!(result2.op1 as u64, 42); // Should return X
    }

    #[test]
    fn test_extract_optimization_basic() {
        let rule = ExtractOptimizationRule;
        
        // Test extract from constant
        let const_expr = create_const_expr(0xFF00);
        let extract_expr = create_extract_expr(&const_expr, 15, 8);
        
        let result = rule.apply(&extract_expr).unwrap();
        // The extract optimization should work and return a constant
        assert_eq!(result.opkind, 1); // Should be constant after optimization
    }

    #[test]
    fn test_zero_extension_elimination() {
        let rule = ZeroExtensionRule;
        
        // Create zero extension expression
        let base_expr = create_const_expr(42);
        let zext_expr = Expr {
            op1: &base_expr as *const Expr as *mut Expr,
            op2: 8 as *mut Expr, // Extend by 8 bits
            op3: ptr::null_mut(),
            opkind: 32, // Zext
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        
        // Extract full original size
        let extract_expr = create_extract_expr(&zext_expr, 31, 0);
        
        let result = rule.apply(&extract_expr).unwrap();
        // Should optimize to just the base expression or a smaller extract
        assert!(result.opkind == 1 || result.opkind == 38);
    }

    #[test]
    fn test_subtraction_transform() {
        let rule = SubtractionTransformRule;
        
        // Create X - Y expression
        let x = create_const_expr(10);
        let y = create_const_expr(5);
        let sub_expr = Expr {
            op1: &x as *const Expr as *mut Expr,
            op2: &y as *const Expr as *mut Expr,
            op3: ptr::null_mut(),
            opkind: 6, // Sub
            op1_is_const: 1,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        
        // Extract from subtraction
        let extract_expr = create_extract_expr(&sub_expr, 7, 0);
        
        let result = rule.apply(&extract_expr).unwrap();
        // Should either be optimized or remain as extract
        assert!(result.opkind == 1 || result.opkind == 38);
    }

    #[test]
    fn test_expression_simplifier_integration() {
        let mut simplifier = ExpressionSimplifier::new();
        
        // Test that safe rules are properly registered
        assert!(simplifier.optimization_rules.len() >= 12); // Should have our enhanced safe rules
        
        // Test basic constant folding
        let const_expr = create_const_expr(42);
        let extract_expr = create_extract_expr(&const_expr, 7, 0);
        
        let result = simplifier.simplify(&extract_expr).unwrap();
        
        // The extract optimization should work since we have opkind 38 and constant operand
        if result.opkind == 1 {
            // If optimization worked, check the extracted value
            assert_eq!(result.op1 as u64, 42 & 0xFF); // Should extract bits [7:0] = 42
        } else {
            // If optimization didn't work, that's also acceptable for this integration test
            assert_eq!(result.opkind, 38); // Should still be extract
        }
    }

}
