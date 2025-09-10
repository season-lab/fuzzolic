use anyhow::Result;
use std::collections::HashMap;
use std::time::Instant;
use crate::Expr;
use crate::expressions::arena::{tls_alloc_opt};
use crate::utils::statistics::Statistics;
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

    /// Simplify an expression using all registered rules with timing statistics
    pub fn simplify_with_stats(&mut self, expr: &Expr, stats: &mut Statistics) -> Result<Expr> {
        let start_time = Instant::now();
        let result = self.simplify_recursive(expr);
        let elapsed = start_time.elapsed();
        stats.simplification_time += elapsed.as_micros() as u64;
        result
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