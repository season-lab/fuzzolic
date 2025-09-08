// use crate::expression::{Expr, OpKind}; // Currently unused
use z3::{ast::Dynamic, Context};
use anyhow::Result;
use std::collections::HashMap;

/// Maximum recursion depth for concrete evaluation
const MAX_EVAL_DEPTH: u32 = 1000;

/// Concrete evaluation engine for symbolic expressions
pub struct ConcreteEvaluator {
    /// Evaluation cache for performance
    eval_cache: HashMap<usize, CachedValue>,
    /// Global cache for cross-query optimization
    global_cache: HashMap<usize, u64>,
    /// Blacklisted inputs for cache invalidation
    blacklist_inputs: HashMap<u64, bool>,
    /// AST to inputs mapping
    ast_to_inputs: HashMap<usize, Vec<u64>>,
    /// Statistics
    eval_count: u64,
    eval_time: u64,
    global_cache_hits: u64,
    global_cache_lookups: u64,
    local_cache_hits: u64,
    local_cache_lookups: u64,
}

#[derive(Clone, Debug)]
struct CachedValue {
    value: u64,
    valid: bool,
}

impl ConcreteEvaluator {
    pub fn new() -> Self {
        Self {
            eval_cache: HashMap::new(),
            global_cache: HashMap::new(),
            blacklist_inputs: HashMap::new(),
            ast_to_inputs: HashMap::new(),
            eval_count: 0,
            eval_time: 0,
            global_cache_hits: 0,
            global_cache_lookups: 0,
            local_cache_hits: 0,
            local_cache_lookups: 0,
        }
    }
    
    /// Hash string like in C implementation
    #[allow(dead_code)]
    fn hash_str(&self, s: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        s.hash(&mut hasher);
        hasher.finish()
    }
    
    /// Concrete evaluation with caching (from eval.c)
    pub fn conc_eval(&mut self, 
                     ctx: &Context,
                     expr: &Dynamic,
                     input_data: &[u8],
                     _others: &HashMap<u64, u64>) -> Result<(u64, bool)> {
        let hash = self.get_ast_id(expr);
        let _from_cache = false;
        
        // Check local cache first
        self.local_cache_lookups += 1;
        if let Some(cached) = self.eval_cache.get(&hash) {
            if cached.valid {
                self.local_cache_hits += 1;
                return Ok((cached.value, true));
            }
        }
        
        // Check global cache if not blacklisted
        let skip_global_cache = self.should_skip_global_cache(hash);
        if !skip_global_cache {
            self.global_cache_lookups += 1;
            if let Some(&value) = self.global_cache.get(&hash) {
                self.global_cache_hits += 1;
                return Ok((value, true));
            }
        }
        
        // Evaluate expression
        let result = self.eval_expr_recursive(ctx, expr, input_data, _others)?;
        
        // Cache the result
        if !skip_global_cache {
            self.global_cache.insert(hash, result);
        }
        
        self.eval_cache.insert(hash, CachedValue {
            value: result,
            valid: true,
        });
        
        Ok((result, false))
    }
    
    fn get_ast_id(&self, expr: &Dynamic) -> usize {
        // Simple hash of expression string representation
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        expr.to_string().hash(&mut hasher);
        hasher.finish() as usize
    }
    
    fn should_skip_global_cache(&self, hash: usize) -> bool {
        // Check if this expression hash is blacklisted
        self.blacklist_inputs.get(&(hash as u64)).copied().unwrap_or(false)
    }
    
    /// Get inputs for expression (from eval.c get_inputs_expr)
    pub fn get_inputs_expr(&mut self, expr: &Dynamic) -> Vec<u64> {
        let hash = self.get_ast_id(expr);
        if let Some(inputs) = self.ast_to_inputs.get(&hash) {
            return inputs.clone();
        }

        let mut inputs = Vec::new();
        self.collect_inputs_structural(expr, &mut inputs);

        // Fallback to string scan only if structural traversal found nothing
        if inputs.is_empty() {
            self.collect_inputs_string(expr, &mut inputs);
        }

        self.ast_to_inputs.insert(hash, inputs.clone());
        inputs
    }

    /// Structural traversal of Z3 AST to collect input_# symbols.
    fn collect_inputs_structural(&self, expr: &Dynamic, inputs: &mut Vec<u64>) {
        use z3::ast::Ast;
        // If it's a constant, try to read its name via to_string()
        if expr.is_const() {
            let s = expr.to_string();
            if let Some(id) = Self::parse_input_symbol(&s) {
                if !inputs.contains(&id) { inputs.push(id); }
            }
            // Constants have no children; return
            return;
        }

        // Recurse into children
        for child in expr.children() {
            self.collect_inputs_structural(&child, inputs);
        }
    }

    /// Fallback: scan string form to find any lingering input_# substrings
    fn collect_inputs_string(&self, expr: &Dynamic, inputs: &mut Vec<u64>) {
        let expr_str = expr.to_string();
        for token in expr_str.split(|c: char| c.is_whitespace() || c == '(' || c == ')' ) {
            if let Some(id) = Self::parse_input_symbol(token) {
                if !inputs.contains(&id) { inputs.push(id); }
            }
        }
    }

    /// Parse an input symbol of the form "input_<id>" and return the id.
    fn parse_input_symbol(s: &str) -> Option<u64> {
        if let Some(rest) = s.strip_prefix("input_") {
            // Allow trailing characters like sort annotations rarely present in Z3 prints
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            if !digits.is_empty() {
                if let Ok(id) = digits.parse::<u64>() { return Some(id); }
            }
        }
        None
    }
    
    /// Fuzzy query evaluation (from eval.c fuzz_query_eval)
    pub fn fuzz_query_eval(&mut self,
                          ctx: &Context,
                          inputs: &[u64],
                          expr: &Dynamic,
                          solutions: &mut std::collections::HashSet<u64>) -> Result<bool> {
        // Implement fuzzy evaluation logic from C version
        // This involves iterating through input values and checking satisfiability
        
        for &input_val in inputs {
            // Create a simple evaluation context with this input value
            let input_data = vec![input_val];
            let symbols_sizes = vec![8u8]; // Assume 8-bit symbols
            
            // Evaluate the expression with this input
            match self.eval_query(ctx, expr, &input_data, &symbols_sizes, MAX_EVAL_DEPTH) {
                Ok(result) => {
                    if result != 0 {
                        solutions.insert(input_val);
                    }
                },
                Err(_) => {
                    // Skip evaluation errors
                    continue;
                }
            }
        }
        
        Ok(solutions.len() > 1)
    }

    /// Evaluate a query concretely using provided input data
    pub fn eval_query(&mut self, 
                     ctx: &Context,
                     query: &Dynamic, 
                     input_data: &[u64],
                     symbols_sizes: &[u8],
                     max_depth: u32) -> Result<u64> {
        let start_time = std::time::Instant::now();
        let result = self.eval_query_recursive(ctx, query, input_data, symbols_sizes, 0, max_depth)?;
        
        self.eval_time += start_time.elapsed().as_micros() as u64;
        self.eval_count += 1;
        
        Ok(result)
    }

    /// Recursive expression evaluation (from eval-driver.c __evaluate_expression)
    fn eval_expr_recursive(&mut self,
                          ctx: &Context,
                          expr: &Dynamic,
                          input_data: &[u8],
                          _others: &HashMap<u64, u64>) -> Result<u64> {
        // This implements the core evaluation logic from eval-driver.c
        // Convert input_data to u64 format for evaluation
        let input_u64: Vec<u64> = input_data.iter().map(|&b| b as u64).collect();
        let symbols_sizes = vec![8u8; input_data.len()]; // Assume 8-bit symbols
        
        // Use the main evaluation function
        self.eval_query(ctx, expr, &input_u64, &symbols_sizes, MAX_EVAL_DEPTH)
    }
    
    /// Recursive concrete evaluation implementation
    fn eval_query_recursive(&mut self,
                           ctx: &Context,
                           expr: &Dynamic,
                           input_data: &[u64],
                           symbols_sizes: &[u8],
                           depth: u32,
                           max_depth: u32) -> Result<u64> {
        if depth > max_depth {
            anyhow::bail!("Maximum evaluation depth exceeded");
        }

        // Check cache first
        let key = self.generate_expr_key(expr);
        if let Some(cached_result) = self.eval_cache.get(&key) {
            return Ok(cached_result.value);
        }

        let expr_kind = self.get_expr_kind(ctx, expr)?;
        let result = match expr_kind {
            ExprKind::Constant(val) => val,
            ExprKind::Symbol(symbol_id) => {
                if (symbol_id as usize) < input_data.len() {
                    input_data[symbol_id as usize] as u64
                } else {
                    0 // Default value for out-of-bounds symbols
                }
            }
            ExprKind::BinaryOp { op, left, right } => {
                let left_val = self.eval_query_recursive(ctx, &left, input_data, symbols_sizes, depth + 1, max_depth)?;
                let right_val = self.eval_query_recursive(ctx, &right, input_data, symbols_sizes, depth + 1, max_depth)?;
                self.eval_binary_op(op, left_val, right_val)?
            }
            ExprKind::UnaryOp { op, operand } => {
                let operand_val = self.eval_query_recursive(ctx, &operand, input_data, symbols_sizes, depth + 1, max_depth)?;
                self.eval_unary_op(op, operand_val)?
            }
            ExprKind::Extract { expr, high, low } => {
                let expr_val = self.eval_query_recursive(ctx, &expr, input_data, symbols_sizes, depth + 1, max_depth)?;
                self.extract_bits(expr_val, high, low)
            }
            ExprKind::Concat { left, right } => {
                let left_val = self.eval_query_recursive(ctx, &left, input_data, symbols_sizes, depth + 1, max_depth)?;
                let right_val = self.eval_query_recursive(ctx, &right, input_data, symbols_sizes, depth + 1, max_depth)?;
                self.concat_values(left_val, right_val)
            }
            ExprKind::Unknown => 0, // Default value for unknown expressions
        };

        // Cache the result
        self.eval_cache.insert(key, CachedValue {
            value: result,
            valid: true,
        });
        Ok(result)
    }

    /// Generate a cache key from expression
    fn generate_expr_key(&self, expr: &Dynamic) -> usize {
        // Use the string representation hash as a simple key
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let expr_str = expr.to_string();
        let mut hasher = DefaultHasher::new();
        expr_str.hash(&mut hasher);
        hasher.finish() as usize
    }

    /// Get expression kind from Z3 Dynamic expression
    fn get_expr_kind(&self, _ctx: &Context, expr: &Dynamic) -> Result<ExprKind<'static>> {
        // Analyze the Z3 expression to determine its kind
        use z3::ast::Ast;
        
        // Check if it's a constant
        if let Some(bv) = expr.as_bv() {
            if let Some(val) = bv.as_u64() {
                return Ok(ExprKind::Constant(val));
            }
        }
        
        // Check if it's a boolean constant
        if let Some(bool_ast) = expr.as_bool() {
            if let Some(val) = bool_ast.as_bool() {
                return Ok(ExprKind::Constant(if val { 1 } else { 0 }));
            }
        }
        
        // Check if it's an application (function call)
        if expr.is_app() {
            // For now, we can't easily extract the operation type from Z3 Rust API
            // This would require more complex Z3 AST analysis
            // Return Unknown for now, but the evaluation will still work for constants
            return Ok(ExprKind::Unknown);
        }
        
        // Check if it looks like a symbol based on string representation
        let expr_str = expr.to_string();
        if expr_str.starts_with("input_") {
            if let Some(id_str) = expr_str.strip_prefix("input_") {
                if let Ok(id) = id_str.parse::<u32>() {
                    return Ok(ExprKind::Symbol(id));
                }
            }
        }
        
        Ok(ExprKind::Unknown)
    }

    /// Evaluate binary operations
    fn eval_binary_op(&self, op: BinaryOp, left: u64, right: u64) -> Result<u64> {
        let result = match op {
            BinaryOp::Add => left.wrapping_add(right),
            BinaryOp::Sub => left.wrapping_sub(right),
            BinaryOp::Mul => left.wrapping_mul(right),
            BinaryOp::Div => if right != 0 { left / right } else { 0 },
            BinaryOp::Mod => if right != 0 { left % right } else { 0 },
            BinaryOp::And => left & right,
            BinaryOp::Or => left | right,
            BinaryOp::Xor => left ^ right,
            BinaryOp::Shl => left << (right & 63), // Limit shift to avoid overflow
            BinaryOp::Shr => left >> (right & 63),
            BinaryOp::Eq => if left == right { 1 } else { 0 },
            BinaryOp::Ne => if left != right { 1 } else { 0 },
            BinaryOp::Lt => if left < right { 1 } else { 0 },
            BinaryOp::Le => if left <= right { 1 } else { 0 },
            BinaryOp::Gt => if left > right { 1 } else { 0 },
            BinaryOp::Ge => if left >= right { 1 } else { 0 },
        };
        Ok(result)
    }

    /// Evaluate unary operations
    fn eval_unary_op(&self, op: UnaryOp, operand: u64) -> Result<u64> {
        let result = match op {
            UnaryOp::Not => !operand,
            UnaryOp::Neg => operand.wrapping_neg(),
        };
        Ok(result)
    }

    /// Evaluate bit extraction
    #[allow(dead_code)]
    fn eval_extract(&self, value: u64, high: u32, low: u32) -> Result<u64> {
        if high < low {
            return Ok(0);
        }
        
        let width = high - low + 1;
        let mask = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
        Ok((value >> low) & mask)
    }

    /// Evaluate concatenation
    #[allow(dead_code)]
    fn eval_concat(&self, left: u64, right: u64) -> Result<u64> {
        // Simple concatenation - in practice this would need size information
        Ok((left << 32) | (right & 0xFFFFFFFF))
    }

    /// Get evaluation statistics
    pub fn stats(&self) -> EvalStats {
        EvalStats {
            eval_count: self.eval_count,
            eval_time: self.eval_time,
            cache_size: self.eval_cache.len(),
        }
    }

    /// Extract bits from a value
    fn extract_bits(&self, value: u64, high: u32, low: u32) -> u64 {
        let width = high - low + 1;
        let mask = (1u64 << width) - 1;
        (value >> low) & mask
    }

    /// Concatenate two values
    fn concat_values(&self, left: u64, right: u64) -> u64 {
        // Simple concatenation - assumes 32-bit values for now
        (left << 32) | (right & 0xFFFFFFFF)
    }

    /// Clear evaluation cache
    pub fn clear_cache(&mut self) {
        self.eval_cache.clear();
    }
}

/// Expression kind for concrete evaluation
#[allow(dead_code)]
#[derive(Debug, Clone)]
enum ExprKind<'a> {
    Constant(u64),
    Symbol(u32),
    BinaryOp { op: BinaryOp, left: Dynamic<'a>, right: Dynamic<'a> },
    UnaryOp { op: UnaryOp, operand: Dynamic<'a> },
    Extract { expr: Dynamic<'a>, high: u32, low: u32 },
    Concat { left: Dynamic<'a>, right: Dynamic<'a> },
    Unknown,
}

/// Binary operations
#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
enum BinaryOp {
    Add, Sub, Mul, Div, Mod,
    And, Or, Xor, Shl, Shr,
    Eq, Ne, Lt, Le, Gt, Ge,
}

/// Unary operations
#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
enum UnaryOp {
    Not, Neg,
}

/// Evaluation statistics
#[derive(Debug, Clone)]
pub struct EvalStats {
    pub eval_count: u64,
    pub eval_time: u64,
    pub cache_size: usize,
}

impl std::fmt::Display for EvalStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Concrete eval: {} queries, {}μs total, {} cached",
               self.eval_count, self.eval_time, self.cache_size)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_operations() {
        let evaluator = ConcreteEvaluator::new();
        
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Add, 5, 3).unwrap(), 8);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Sub, 5, 3).unwrap(), 2);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Mul, 5, 3).unwrap(), 15);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Div, 15, 3).unwrap(), 5);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::And, 0b1010, 0b1100).unwrap(), 0b1000);
        assert_eq!(evaluator.eval_binary_op(BinaryOp::Or, 0b1010, 0b1100).unwrap(), 0b1110);
    }

    #[test]
    fn test_extract() {
        let evaluator = ConcreteEvaluator::new();
        
        // Extract bits [7:4] from 0xFF (should be 0xF)
        assert_eq!(evaluator.eval_extract(0xFF, 7, 4).unwrap(), 0xF);
        
        // Extract bits [3:0] from 0xFF (should be 0xF)
        assert_eq!(evaluator.eval_extract(0xFF, 3, 0).unwrap(), 0xF);
    }
}
