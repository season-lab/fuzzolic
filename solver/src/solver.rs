use crate::expression::{Expr, DependencyGraph};
use crate::expression_simplifier::ExpressionSimplifier;
use crate::{BranchCoverage, Testcase};
use crate::i386;
use crate::fuzzy_ffi::{fuzz_bridge_init, fuzz_bridge_check_light, fuzz_bridge_get_optimistic, raw_ast_from_bool, raw_ctx_from_bool, fuzz_bridge_get_stats, FuzzBridgeStats, fuzz_bridge_free};
use z3::{Context, ast::{Ast, Bool}};
use std::os::raw::c_void;
use anyhow::Result;
use log::info;
use crate::statistics::Statistics;

// Statistics are now provided by crate::statistics::Statistics

/// Public statistics structure for external use
#[derive(Debug, Clone)]
pub struct SolverStatistics {
    pub queries_processed: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub timeout_count: u64,
    pub translation_time: u64,
    pub solving_time: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub optimization_count: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{Expr, OpKind};

    fn ctx() -> z3::Context {
        let mut cfg = z3::Config::new();
        // Keep defaults; tests do not need special params
        z3::Context::new(&cfg)
    }

    #[test]
    fn test_translate_symbolic_jump_table_access() {
        let c = ctx();
        let expr = Expr {
            op1: std::ptr::null_mut(),
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::SymbolicJumpTableAccess as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        };
        let dyn_ast = SMTSolver::translate_expression_static(&c, &expr).expect("translate ok");
        let bv = dyn_ast.as_bv().expect("jump table access yields BV");
        assert_eq!(bv.get_size(), 64);
    }

    #[test]
    fn test_translate_memory_slice() {
        let c = ctx();
        // MemorySlice with base encoded as const in op1 and size=2 bytes
        let expr = Expr {
            op1: 0x1234usize as *mut Expr, // const base
            op2: 2usize as *mut Expr,      // size in bytes
            op3: std::ptr::null_mut(),
            opkind: OpKind::MemorySlice as u8,
            op1_is_const: 1,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        let dyn_ast = SMTSolver::translate_expression_static(&c, &expr).expect("translate ok");
        let bv = dyn_ast.as_bv().expect("memory slice yields BV");
        assert_eq!(bv.get_size(), 16); // 2 bytes * 8 = 16 bits
    }
}
impl Drop for SMTSolver {
    fn drop(&mut self) {
        if !self.fuzzy_ctx.is_null() {
            unsafe { fuzz_bridge_free(self.fuzzy_ctx) };
            self.fuzzy_ctx = std::ptr::null_mut();
        }
    }
}

pub struct SMTSolver {
    pub ctx: Context,
    branch_coverage: Option<BranchCoverage>,
    statistics: Statistics,
    pub current_testcase: Option<Testcase>,
    dependency_graph: DependencyGraph,
    translation_cache: std::cell::RefCell<std::collections::HashMap<u64, String>>,
    // Cross-query caches of dependency expression kinds (Bool vs non-Bool),
    // keyed by raw Expr pointer address (usize). We avoid SMT-LIB strings.
    pub(crate) dep_bool_ids: std::cell::RefCell<std::collections::HashSet<usize>>,
    pub(crate) dep_nonbool_ids: std::cell::RefCell<std::collections::HashSet<usize>>,
    // Optional conservative expression simplifier gated via config
    use_expr_simplifier: bool,
    expr_simplifier: Option<std::cell::RefCell<ExpressionSimplifier>>,
    // Fuzzy solver interop
    fuzzy_enabled: bool,
    fuzzy_timeout_ms: u32,
    fuzzy_ctx: *mut c_void,
}

impl SMTSolver {
    pub fn new(config: &crate::Config) -> Result<Self> {
        let z3_config = z3::Config::new();
        let ctx = Context::new(&z3_config);
        
        let branch_coverage = if config.use_branch_coverage {
            Some(BranchCoverage::new(config)?)
        } else {
            None
        };
        
        Ok(SMTSolver {
            ctx,
            branch_coverage,
            statistics: Statistics::default(),
            current_testcase: None,
            dependency_graph: DependencyGraph::new(),
            translation_cache: std::cell::RefCell::new(std::collections::HashMap::new()),
            dep_bool_ids: std::cell::RefCell::new(std::collections::HashSet::new()),
            dep_nonbool_ids: std::cell::RefCell::new(std::collections::HashSet::new()),
            use_expr_simplifier: config.use_expr_simplifier,
            expr_simplifier: if config.use_expr_simplifier { Some(std::cell::RefCell::new(ExpressionSimplifier::new_conservative())) } else { None },
            fuzzy_enabled: config.use_fuzzy_solver,
            fuzzy_timeout_ms: config.fuzzy_timeout_ms(),
            fuzzy_ctx: std::ptr::null_mut(),
        })
    }

    /// Pull fuzzy stats from C and update our Statistics
    fn pull_fuzzy_stats(&mut self) {
        if self.fuzzy_ctx.is_null() { return; }
        let mut s = FuzzBridgeStats::default();
        unsafe { fuzz_bridge_get_stats(self.fuzzy_ctx, &mut s as *mut FuzzBridgeStats) };
        // Map a subset into our stats. We only have num_evaluate->translation_time-ish proxy, and sat/timeout counts
        self.statistics.fuzzy_num_evaluate = s.num_evaluate as u64;
        self.statistics.fuzzy_num_sat = s.num_sat as u64;
        self.statistics.fuzzy_num_timeouts = s.num_timeouts as u64;
    }

    /// Public hook to refresh fuzzy stats before printing
    pub fn refresh_fuzzy_stats(&mut self) { self.pull_fuzzy_stats(); }
    
    pub fn initialize(&mut self) -> Result<()> {
        // Initialize solver components
        // SharedMemoryManager doesn't have initialize method - it's initialized in constructor
        Ok(())
    }

    /// Record dependency information for an expression into the dependency graph.
    /// Uses the Z3 translation to extract symbolic input IDs and links them to the expression ID.
    /// The expression ID is derived from the pointer address to mirror the C-side identity.
    pub fn add_dependency_for_expr(&mut self, expr: &Expr) -> Result<()> {
        // Translate once to Z3 to extract inputs via ConcreteEvaluator
        let z3_expr = Self::translate_expression_static(&self.ctx, expr)?;
        let mut evaluator = crate::concrete_eval::ConcreteEvaluator::new();
        let inputs = evaluator.get_inputs_expr(&z3_expr);

        // Use the address of the Expr as a stable identifier
        let expr_id = expr as *const Expr as usize;
        for input_id in inputs {
            // Our dependency graph is keyed by input id -> expressions
            self.dependency_graph.add_dependency(input_id as usize, expr_id);
        }
        Ok(())
    }

    /// Retrieve merged dependencies information for a set of input IDs.
    pub fn get_deps_for_inputs(
        &self,
        inputs: &std::collections::HashSet<usize>,
    ) -> crate::expression::Dependency {
        self.dependency_graph.merge_dependencies(inputs)
    }

    /// Mark an expression ID as Bool-producing.
    fn mark_dep_bool_id(&self, id: usize) {
        self.dep_bool_ids.borrow_mut().insert(id);
        self.dep_nonbool_ids.borrow_mut().remove(&id);
    }

    /// Mark an expression ID as non-Bool-producing.
    fn mark_dep_nonbool_id(&self, id: usize) {
        self.dep_nonbool_ids.borrow_mut().insert(id);
        self.dep_bool_ids.borrow_mut().remove(&id);
    }

    /// Check known kind caches.
    pub fn is_dep_bool_id(&self, id: usize) -> bool { self.dep_bool_ids.borrow().contains(&id) }
    pub fn is_dep_nonbool_id(&self, id: usize) -> bool { self.dep_nonbool_ids.borrow().contains(&id) }

    /// Ensure we know whether an expression is Bool-producing. Returns true if Bool.
    pub fn ensure_dep_is_bool(&self, expr: &Expr) -> bool {
        let id = expr as *const Expr as usize;
        if self.is_dep_bool_id(id) { return true; }
        if self.is_dep_nonbool_id(id) { return false; }
        match Self::translate_expression_static(&self.ctx, expr) {
            Ok(ast) => {
                if ast.as_bool().is_some() { self.mark_dep_bool_id(id); true } else { self.mark_dep_nonbool_id(id); false }
            }
            Err(_) => { self.mark_dep_nonbool_id(id); false }
        }
    }
    
    pub fn get_current_testcase(&self) -> Option<Vec<u8>> {
        self.current_testcase.as_ref().map(|t| t.data.clone())
    }
    
    pub fn print_statistics(&self) {
        // Note: fuzzy stats come from C; ensure we print latest values
        println!("SMT Solver Statistics:");
        println!("  Queries processed: {}", self.statistics.queries_processed);
        println!("  Timeout count: {}", self.statistics.timeout_count);
        println!("  Translation time: {}ms", self.statistics.translation_time);
        println!("  Solving time: {}ms", self.statistics.solving_time);
        println!("  Cache hits: {}", self.statistics.cache_hits);
        println!("  Cache misses: {}", self.statistics.cache_misses);
        println!("  Fuzzy num_evaluate: {}", self.statistics.fuzzy_num_evaluate);
        println!("  Fuzzy num_sat: {}", self.statistics.fuzzy_num_sat);
        println!("  Fuzzy num_timeouts: {}", self.statistics.fuzzy_num_timeouts);
    }

    /// Notify the fuzzy engine about a newly added constraint (mirrors z3fuzz_notify_constraint)
    /// Note: does not initialize the fuzzy context; assumes it is already initialized elsewhere.
    pub fn fuzzy_notify_constraint(&self, constraint: &Bool) {
        if !self.fuzzy_enabled || self.fuzzy_ctx.is_null() { return; }
        unsafe {
            crate::fuzzy_ffi::fuzz_bridge_notify_constraint(
                self.fuzzy_ctx,
                crate::fuzzy_ffi::raw_ast_from_bool(constraint),
            );
        }
    }
    
    /// Initialize fuzzy context (once), using the same Z3 context as the Rust solver.
    fn init_fuzzy_once(&mut self) -> anyhow::Result<()> {
        if !self.fuzzy_enabled { return Ok(()); }
        if !self.fuzzy_ctx.is_null() { return Ok(()); }
        // Build a dummy Bool to extract Z3_context safely via raw helpers
        let true_b = Bool::from_bool(&self.ctx, true);
        let z3_ctx = unsafe { raw_ctx_from_bool(&true_b) };
        // Use configured fuzzy timeout
        let ptr = unsafe { fuzz_bridge_init(z3_ctx, self.fuzzy_timeout_ms) };
        self.fuzzy_ctx = ptr;
        Ok(())
    }

    /// Call C fuzzy solver fast checker via bridge: fuzz_bridge_check_light
    pub fn fuzzy_check_light(&mut self, fuzzy_query: &Bool, neg_query: &Bool) -> anyhow::Result<bool> {
        if !self.fuzzy_enabled { return Ok(false); }
        self.init_fuzzy_once()?;
        if self.fuzzy_ctx.is_null() { return Ok(false); }
        let query_raw = unsafe { raw_ast_from_bool(fuzzy_query) };
        let neg_raw = unsafe { raw_ast_from_bool(neg_query) };
        self.fuzzy_check_light_raw(query_raw, neg_raw)
    }

    /// Call the optimistic solver fallback (from C: z3fuzz_get_optimistic_sol)
    pub fn fuzzy_get_optimistic(&mut self) -> anyhow::Result<bool> {
        if !self.fuzzy_enabled { return Ok(false); }
        self.init_fuzzy_once()?;
        if self.fuzzy_ctx.is_null() { return Ok(false); }
        let mut proof: *const u8 = std::ptr::null();
        let mut proof_len: u64 = 0;
        let r = unsafe { fuzz_bridge_get_optimistic(self.fuzzy_ctx, &mut proof, &mut proof_len) };
        // Update basic stats from C
        self.pull_fuzzy_stats();
        Ok(r != 0)
    }

    /// Raw-pointer variant to avoid holding immutable borrows of Z3 context across the call.
    pub fn fuzzy_check_light_raw(&mut self, query_raw: *mut c_void, neg_raw: *mut c_void) -> anyhow::Result<bool> {
        if !self.fuzzy_enabled { return Ok(false); }
        self.init_fuzzy_once()?;
        if self.fuzzy_ctx.is_null() { return Ok(false); }
        let mut proof: *const u8 = std::ptr::null();
        let mut proof_len: u64 = 0;
        let r = unsafe { fuzz_bridge_check_light(self.fuzzy_ctx, query_raw, neg_raw, &mut proof, &mut proof_len) };
        // Update fuzzy stats from C after each call
        self.pull_fuzzy_stats();
        Ok(r != 0)
    }
    
    pub fn solve_query(&mut self, expr: &Expr) -> Result<crate::expression::SatResult> {
        let z3_expr = self.translate_expression(expr)?;
        let solver = z3::Solver::new(&self.ctx);
        solver.assert(&z3_expr.as_bool().unwrap());
        
        match solver.check() {
            z3::SatResult::Sat => Ok(crate::expression::SatResult::Sat),
            z3::SatResult::Unsat => Ok(crate::expression::SatResult::Unsat),
            z3::SatResult::Unknown => Ok(crate::expression::SatResult::Unknown),
        }
    }
    
    /// Load initial testcase if available
    pub fn load_initial_testcase(&mut self) -> Result<bool> {
        if let Some(testcase) = &self.current_testcase {
            info!("Loaded initial testcase with {} bytes", testcase.data.len());
            Ok(true)
        } else {
            Ok(false)
        }
    }
    
    pub fn save_state(&self) -> Result<()> {
        // Save solver state and statistics
        info!("Saving solver state");
        if let Some(ref branch_coverage) = self.branch_coverage {
            branch_coverage.save_bitmaps()?;
        }
        Ok(())
    }

    pub fn translate_expr_to_z3<'a>(&'a self, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        self.translate_expression(expr)
    }
    
    /// Helper: translate an operand that can be either a constant (embedded in the pointer)
    /// or a pointer to another Expr node. Mirrors the C-side encoding using op*_is_const flags.
    fn translate_operand_static<'a>(ctx: &'a z3::Context, operand: *mut Expr, is_const: u8) -> Result<z3::ast::Dynamic<'a>> {
        if is_const != 0 {
            let value = operand as u64;
            // Default to 64-bit BV for constants. Callers can reinterpret as needed.
            Ok(z3::ast::BV::from_u64(ctx, value, 64).into())
        } else {
            if operand.is_null() {
                anyhow::bail!("Null (non-const) operand encountered in translation")
            }
            // SAFETY: operand points to a valid Expr node provided by QEMU side
            Self::translate_expression_static(ctx, unsafe { &*operand })
        }
    }

    /// Static expression translation method for avoiding borrowing conflicts
    pub fn translate_expression_static<'a>(ctx: &'a z3::Context, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        use crate::expression::OpKind;
        let op = OpKind::try_from(expr.opkind)?;
        match op {
            OpKind::Not => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                if let Some(b) = v.as_bool() { Ok(b.not().into()) } else { Ok(v.as_bv().ok_or_else(|| anyhow::anyhow!("Not op1 not BV/bool"))?.bvnot().into()) }
            }
            OpKind::Neg => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                Ok(v.as_bv().ok_or_else(|| anyhow::anyhow!("Neg op1 not BV"))?.bvneg().into())
            }
            OpKind::IsConst => {
                let value = expr.op1 as u64;
                Ok(z3::ast::BV::from_u64(ctx, value, 64).into())
            }
            // Create a BV symbol for input bytes: input_{id}
            OpKind::IsSymbolic => {
                let input_id = expr.op1 as u64;
                // Default to 8-bit symbols (byte-level) unless size is provided as const in op2
                let n_bits: u32 = if expr.op2_is_const != 0 { (expr.op2 as usize as u32) * 8 } else { 8 };
                let name = format!("input_{}", input_id);
                Ok(z3::ast::BV::new_const(ctx, name, n_bits).into())
            }
            OpKind::Add => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Add lhs not BV"))?
                    .bvadd(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Add rhs not BV"))?)
                    .into())
            }
            OpKind::Sub => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Sub lhs not BV"))?
                    .bvsub(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Sub rhs not BV"))?)
                    .into())
            }
            OpKind::Mul => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Mul lhs not BV"))?
                    .bvmul(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Mul rhs not BV"))?)
                    .into())
            }
            OpKind::Mulu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Mulu lhs not BV"))?
                    .bvmul(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Mulu rhs not BV"))?)
                    .into())
            }
            OpKind::Div => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Div lhs not BV"))?
                    .bvsdiv(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Div rhs not BV"))?)
                    .into())
            }
            OpKind::Divu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Divu lhs not BV"))?
                    .bvudiv(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Divu rhs not BV"))?)
                    .into())
            }
            OpKind::Rem => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Rem lhs not BV"))?
                    .bvsrem(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Rem rhs not BV"))?)
                    .into())
            }
            OpKind::Remu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Remu lhs not BV"))?
                    .bvurem(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Remu rhs not BV"))?)
                    .into())
            }
            OpKind::And => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
                    Ok(z3::ast::Bool::and(ctx, &[&lb, &rb]).into())
                } else {
                    Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("And lhs not BV/bool"))?
                        .bvand(&r.as_bv().ok_or_else(|| anyhow::anyhow!("And rhs not BV/bool"))?)
                        .into())
                }
            }
            OpKind::Or => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
                    Ok(z3::ast::Bool::or(ctx, &[&lb, &rb]).into())
                } else {
                    Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Or lhs not BV/bool"))?
                        .bvor(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Or rhs not BV/bool"))?)
                        .into())
                }
            }
            OpKind::Xor => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Xor lhs not BV"))?
                    .bvxor(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Xor rhs not BV"))?)
                    .into())
            }
            OpKind::Shl | OpKind::Sal => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Shl lhs not BV"))?
                    .bvshl(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Shl rhs not BV"))?)
                    .into())
            }
            OpKind::Shr => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Shr lhs not BV"))?
                    .bvlshr(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Shr rhs not BV"))?)
                    .into())
            }
            OpKind::Sar => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Sar lhs not BV"))?
                    .bvashr(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Sar rhs not BV"))?)
                    .into())
            }
            OpKind::Eq => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l._eq(&r).into())
            }
            OpKind::Ne => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l._eq(&r).not().into())
            }
            OpKind::Lt => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Lt lhs not BV"))?
                    .bvslt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Lt rhs not BV"))?)
                    .into())
            }
            OpKind::Le => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Le lhs not BV"))?
                    .bvsle(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Le rhs not BV"))?)
                    .into())
            }
            OpKind::Gt => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Gt lhs not BV"))?
                    .bvsgt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Gt rhs not BV"))?)
                    .into())
            }
            OpKind::Ge => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Ge lhs not BV"))?
                    .bvsge(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Ge rhs not BV"))?)
                    .into())
            }
            OpKind::Ltu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Ltu lhs not BV"))?
                    .bvult(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Ltu rhs not BV"))?)
                    .into())
            }
            OpKind::Leu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Leu lhs not BV"))?
                    .bvule(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Leu rhs not BV"))?)
                    .into())
            }
            OpKind::Gtu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Gtu lhs not BV"))?
                    .bvugt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Gtu rhs not BV"))?)
                    .into())
            }
            OpKind::Geu => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Geu lhs not BV"))?
                    .bvuge(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Geu rhs not BV"))?)
                    .into())
            }
            OpKind::Extract => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Extract op1 not BV"))?;
                if expr.op2_is_const == 0 || expr.op3_is_const == 0 { anyhow::bail!("Extract requires const high/low indices") }
                let high = expr.op2 as u32;
                let low = expr.op3 as u32;
                Ok(bv.extract(high, low).into())
            }
            OpKind::Extract8 => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Extract8 op1 not BV"))?;
                if expr.op2_is_const == 0 { anyhow::bail!("Extract8 requires const byte index") }
                let byte_index = expr.op2 as u32;
                let high = ((byte_index + 1) * 8) - 1;
                let low = byte_index * 8;
                Ok(bv.extract(high, low).into())
            }
            OpKind::Concat => {
                let l = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let r = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Concat lhs not BV"))?
                    .concat(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Concat rhs not BV"))?)
                    .into())
            }
            OpKind::Zext => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Zext op1 not BV"))?;
                let target_bits = expr.op2 as u32;
                let cur = bv.get_size();
                let extend_by = if target_bits > cur { target_bits - cur } else { 0 };
                Ok(bv.zero_ext(extend_by).into())
            }
            OpKind::Sext => {
                let v = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Sext op1 not BV"))?;
                let target_bits = expr.op2 as u32;
                let cur = bv.get_size();
                let extend_by = if target_bits > cur { target_bits - cur } else { 0 };
                Ok(bv.sign_ext(extend_by).into())
            }
            // Memory/symbolic ops: model as fresh Z3 symbols to decouple from
            // concrete memory reasoning. Higher layers (MemorySliceReasoner) can
            // optionally add constraints relating these symbols.
            OpKind::MemorySlice => {
                let base = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let size = expr.op2 as u64;
                let base_bv = base.as_bv().ok_or_else(|| anyhow::anyhow!("MemorySlice base not BV"))?;
                let name = format!("slice_{}_{}", base_bv.to_string(), size);
                Ok(z3::ast::BV::new_const(ctx, name, (size * 8) as u32).into())
            }
            OpKind::SymbolicJumpTableAccess => {
                // Model as a fresh 64-bit address symbol. Higher layers may further constrain it.
                let name = format!("jt_access_{}", (expr as *const Expr as usize));
                Ok(z3::ast::BV::new_const(ctx, name, 64).into())
            }
            OpKind::SymbolicLoad => {
                let addr = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let addr_bv = addr.as_bv().ok_or_else(|| anyhow::anyhow!("SymbolicLoad addr not BV"))?;
                let name = format!("load_{}", addr_bv.to_string());
                Ok(z3::ast::BV::new_const(ctx, name, 64).into())
            }
            OpKind::SymbolicStore => {
                let _addr = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let val = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                Ok(val)
            }
            OpKind::Rotl => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let amount = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(op_bv), Some(amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    Ok(op_bv.bvrotl(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Rotl operation")
                }
            }
            OpKind::Rotr => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let amount = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(op_bv), Some(amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    Ok(op_bv.bvrotr(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Rotr operation")
                }
            }
            // Optional Abs implementation (not part of OpKind currently)
            /* 36 => { // Abs (absolute value)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    // Implement abs using ITE: (ite (bvslt x 0) (bvneg x) x)
                    let zero = z3::ast::BV::from_u64(ctx, 0, op_bv.get_size());
                    let is_negative = op_bv.bvslt(&zero);
                    let negated = op_bv.bvneg();
                    Ok(is_negative.ite(&negated.into(), &op_bv.into()))
                } else {
                    anyhow::bail!("Invalid operand for Abs operation")
                }
            } */
            OpKind::Min => {
                let left = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let right = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    // Implement min using ITE: (ite (bvult x y) x y)
                    let is_less = left_bv.bvult(&right_bv);
                    Ok(is_less.ite(&left_bv.into(), &right_bv.into()))
                } else {
                    anyhow::bail!("Invalid operands for Min operation")
                }
            }
            OpKind::Max => {
                let left = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let right = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    // Implement max using ITE: (ite (bvugt x y) x y)
                    let is_greater = left_bv.bvugt(&right_bv);
                    Ok(is_greater.ite(&left_bv.into(), &right_bv.into()))
                } else {
                    anyhow::bail!("Invalid operands for Max operation")
                }
            }
            OpKind::IteEqZero => {
                // (ite (== op1 0) op2 op3) treating op1 as BV if needed
                let c = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let t = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                let e = Self::translate_operand_static(ctx, expr.op3, expr.op3_is_const)?;
                let cond = if let Some(cb) = c.as_bool() {
                    cb._eq(&z3::ast::Bool::from_bool(ctx, true)) // rarely used; prefer BV route
                } else if let Some(cbv) = c.as_bv() {
                    let zero = z3::ast::BV::from_u64(ctx, 0, cbv.get_size());
                    cbv._eq(&zero)
                } else {
                    anyhow::bail!("IteEqZero cond not BV/bool")
                };
                if let (Some(tbv), Some(ebv)) = (t.as_bv(), e.as_bv()) {
                    Ok(cond.ite(&tbv.into(), &ebv.into()))
                } else if let (Some(tb), Some(eb)) = (t.as_bool(), e.as_bool()) {
                    Ok(cond.ite(&tb.into(), &eb.into()))
                } else {
                    anyhow::bail!("IteEqZero branch types mismatch")
                }
            }
            OpKind::IteNeZero => {
                // (ite (!= op1 0) op2 op3)
                let c = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let t = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                let e = Self::translate_operand_static(ctx, expr.op3, expr.op3_is_const)?;
                let cond = if let Some(cb) = c.as_bool() {
                    cb // already boolean
                } else if let Some(cbv) = c.as_bv() {
                    let zero = z3::ast::BV::from_u64(ctx, 0, cbv.get_size());
                    cbv._eq(&zero).not()
                } else {
                    anyhow::bail!("IteNeZero cond not BV/bool")
                };
                if let (Some(tbv), Some(ebv)) = (t.as_bv(), e.as_bv()) {
                    Ok(cond.ite(&tbv.into(), &ebv.into()))
                } else if let (Some(tb), Some(eb)) = (t.as_bool(), e.as_bool()) {
                    Ok(cond.ite(&tb.into(), &eb.into()))
                } else {
                    anyhow::bail!("IteNeZero branch types mismatch")
                }
            }
            OpKind::Nand => {
                let left = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let right = Self::translate_operand_static(ctx, expr.op2, expr.op2_is_const)?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvand(&right_bv).bvnot().into())
                } else {
                    anyhow::bail!("Invalid operands for Nand operation")
                }
            }
            OpKind::Clz => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let op_bv = operand.as_bv().ok_or_else(|| anyhow::anyhow!("Invalid operand for Clz operation"))?;
                let n = op_bv.get_size();
                let zero_n = z3::ast::BV::from_u64(ctx, 0, n);
                let is_zero = op_bv._eq(&zero_n);
                // Build chain: if op==0 then n else first k where high k bits zero and next bit is 1
                let mut acc: z3::ast::Dynamic = z3::ast::BV::from_u64(ctx, n as u64, 64).into();
                for k in (0..n).rev() {
                    // high k bits zero
                    let high_zero = if k == 0 {
                        z3::ast::Bool::from_bool(ctx, true)
                    } else {
                        let hi = n - 1;
                        let lo = n - k;
                        let high = op_bv.extract(hi, lo);
                        high._eq(&z3::ast::BV::from_u64(ctx, 0, k))
                    };
                    // next bit is one at position n-k-1
                    let bit_pos = n - k - 1;
                    let bit = op_bv.extract(bit_pos, bit_pos);
                    let next_one = bit._eq(&z3::ast::BV::from_u64(ctx, 1, 1));
                    let cond = z3::ast::Bool::and(ctx, &[&high_zero, &next_one]);
                    let then_bv = z3::ast::BV::from_u64(ctx, k as u64, 64);
                    acc = cond.ite(&then_bv.into(), &acc);
                }
                // if op==0 then n else acc
                let result = is_zero.ite(&z3::ast::BV::from_u64(ctx, n as u64, 64).into(), &acc);
                Ok(result)
            }
            OpKind::Ctz => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                let op_bv = operand.as_bv().ok_or_else(|| anyhow::anyhow!("Invalid operand for Ctz operation"))?;
                let n = op_bv.get_size();
                let zero_n = z3::ast::BV::from_u64(ctx, 0, n);
                let is_zero = op_bv._eq(&zero_n);
                // Build chain: if op==0 then n else first k where low k bits zero and bit k is 1
                let mut acc: z3::ast::Dynamic = z3::ast::BV::from_u64(ctx, n as u64, 64).into();
                for k in (0..n).rev() {
                    // low k bits zero
                    let low_zero = if k == 0 {
                        z3::ast::Bool::from_bool(ctx, true)
                    } else {
                        let low = op_bv.extract(k - 1, 0);
                        low._eq(&z3::ast::BV::from_u64(ctx, 0, k))
                    };
                    // bit k is one
                    let bit = op_bv.extract(k, k);
                    let bit_one = bit._eq(&z3::ast::BV::from_u64(ctx, 1, 1));
                    let cond = z3::ast::Bool::and(ctx, &[&low_zero, &bit_one]);
                    let then_bv = z3::ast::BV::from_u64(ctx, k as u64, 64);
                    acc = cond.ite(&then_bv.into(), &acc);
                }
                let result = is_zero.ite(&z3::ast::BV::from_u64(ctx, n as u64, 64).into(), &acc);
                Ok(result)
            }
            OpKind::Bswap => {
                let operand = Self::translate_operand_static(ctx, expr.op1, expr.op1_is_const)?;
                if let Some(op_bv) = operand.as_bv() {
                    let size = op_bv.get_size();
                    if size % 8 != 0 { anyhow::bail!("Bswap requires byte-multiple width") }
                    let bytes = size / 8;
                    let mut acc: Option<z3::ast::BV> = None;
                    for i in 0..bytes {
                        let hi = (i + 1) * 8 - 1;
                        let lo = i * 8;
                        let byte = op_bv.extract(hi, lo);
                        acc = Some(match acc { None => byte, Some(a) => byte.concat(&a) });
                    }
                    Ok(acc.unwrap().into())
                } else {
                    anyhow::bail!("Invalid operand for Bswap operation")
                }
            }
            // Delegate i386-specific operations to the i386 translator
            OpKind::CmpEq | OpKind::CmpGt | OpKind::CmpGe | OpKind::CmpLt | OpKind::CmpLe |
            OpKind::Pmovmskb |
            OpKind::EflagsAllAdd | OpKind::EflagsAllSub | OpKind::EflagsAllMul |
            OpKind::EflagsAllLogic | OpKind::EflagsAllInc | OpKind::EflagsAllDec |
            OpKind::EflagsAllShl | OpKind::EflagsAllSar | OpKind::EflagsAllBmilg | OpKind::EflagsAllRcl |
            OpKind::EflagsAllAdcb | OpKind::EflagsAllAdcw | OpKind::EflagsAllAdcl | OpKind::EflagsAllAdcq |
            OpKind::EflagsAllSbbb | OpKind::EflagsAllSbbw | OpKind::EflagsAllSbbl | OpKind::EflagsAllSbbq |
            OpKind::EflagsCAdd | OpKind::EflagsCSub | OpKind::EflagsCMul | OpKind::EflagsCLogic | OpKind::EflagsCShl |
            OpKind::EflagsCAdcb | OpKind::EflagsCAdcw | OpKind::EflagsCAdcl | OpKind::EflagsCAdcq |
            OpKind::EflagsCSbbb | OpKind::EflagsCSbbw | OpKind::EflagsCSbbl | OpKind::EflagsCSbbq |
            OpKind::Rcl => {
                let dyn_ast = i386::smt_query_i386_to_z3(ctx, expr, 8)?;
                Ok(dyn_ast)
            }
            _ => {
                // Enhanced error handling for unsupported operations
                anyhow::bail!("Unsupported OpKind {} in expression translation. This operation is not yet implemented in the Z3 translation layer.", expr.opkind)
            }
        }
    }

    /// Internal expression translation method with optimization
    fn translate_expression<'a>(&'a self, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        // Check for cached translations first
        let expr_hash = self.compute_expression_hash(expr);
        let _cache_key = format!("{}", expr_hash);
        
        if let Some(_cached_result) = self.translation_cache.borrow().get(&expr_hash) {
            // Skip caching due to lifetime issues - translate directly
            // Proper caching would require string-based storage or Arc<> wrappers
        }
        
        // Apply expression optimizations before translation
        let optimized_expr = self.optimize_expression(expr)?;
        
        // Use the static method to avoid borrowing conflicts
        let result = Self::translate_expression_static(&self.ctx, &optimized_expr)?;
        
        // Cache the result as string representation for future reference
        self.translation_cache.borrow_mut().insert(expr_hash, result.to_string());
        
        Ok(result)
    }
    
    /// Compute hash for expression caching
    fn compute_expression_hash(&self, expr: &Expr) -> u64 {
        // Simple hash based on opkind and operand addresses
        let mut hash = expr.opkind as u64;
        hash = hash.wrapping_mul(31).wrapping_add(expr.op1 as u64);
        hash = hash.wrapping_mul(31).wrapping_add(expr.op2 as u64);
        hash = hash.wrapping_mul(31).wrapping_add(expr.op3 as u64);
        hash
    }
    
    /// Optimize expression before translation
    fn optimize_expression(&self, expr: &Expr) -> Result<Expr> {
        // Optional: conservative simplifier pass first
        if self.use_expr_simplifier {
            if let Some(s) = &self.expr_simplifier {
                if let Ok(simpl) = s.borrow_mut().simplify(expr) {
                    return Ok(simpl);
                }
            }
        }
        // Apply various peephole optimizations using OpKind
        use crate::expression::OpKind;
        let kind = OpKind::try_from(expr.opkind)?;
        match kind {
            OpKind::Add => {
                // x + 0 = x ; 0 + x = x
                if self.is_constant_zero(expr.op2) && !expr.op1.is_null() {
                    return Ok(unsafe { (*expr.op1).clone() });
                }
                if self.is_constant_zero(expr.op1) && !expr.op2.is_null() {
                    return Ok(unsafe { (*expr.op2).clone() });
                }
            }
            OpKind::Mul | OpKind::Mulu => {
                // x * 0 = 0 ; 0 * x = 0
                if self.is_constant_zero(expr.op1) || self.is_constant_zero(expr.op2) {
                    return Ok(Expr::new_const(0));
                }
                // x * 1 = x ; 1 * x = x
                if self.is_constant_one(expr.op1) && !expr.op2.is_null() {
                    return Ok(unsafe { (*expr.op2).clone() });
                }
                if self.is_constant_one(expr.op2) && !expr.op1.is_null() {
                    return Ok(unsafe { (*expr.op1).clone() });
                }
            }
            OpKind::And => {
                // x & 0 = 0 ; 0 & x = 0
                if self.is_constant_zero(expr.op1) || self.is_constant_zero(expr.op2) {
                    return Ok(Expr::new_const(0));
                }
            }
            OpKind::Or => {
                // x | 0 = x ; 0 | x = x
                if self.is_constant_zero(expr.op1) && !expr.op2.is_null() {
                    return Ok(unsafe { (*expr.op2).clone() });
                }
                if self.is_constant_zero(expr.op2) && !expr.op1.is_null() {
                    return Ok(unsafe { (*expr.op1).clone() });
                }
            }
            OpKind::Xor => {
                // x ^ 0 = x ; 0 ^ x = x
                if self.is_constant_zero(expr.op2) && !expr.op1.is_null() {
                    return Ok(unsafe { (*expr.op1).clone() });
                }
                if self.is_constant_zero(expr.op1) && !expr.op2.is_null() {
                    return Ok(unsafe { (*expr.op2).clone() });
                }
            }
            _ => {}
        }
        
        // No optimization applied, return original
        Ok(expr.clone())
    }
    /// Check if expression operand is constant zero
    fn is_constant_zero(&self, operand: *mut Expr) -> bool {
        if operand.is_null() {
            return false;
        }
        let expr = unsafe { &*operand };
        expr.opkind == crate::expression::OpKind::IsConst as u8 && expr.op1 as u64 == 0 // Const with value 0
    }
    
    /// Check if expression operand is constant one
    fn is_constant_one(&self, operand: *mut Expr) -> bool {
        if operand.is_null() {
            return false;
        }
        let expr = unsafe { &*operand };
        expr.opkind == crate::expression::OpKind::IsConst as u8 && expr.op1 as u64 == 1 // Const with value 1
    }

    pub fn save_bitmaps(&self) -> anyhow::Result<()> {
        if let Some(ref branch_cov) = self.branch_coverage {
            branch_cov.save_bitmaps()?;
        }
        Ok(())
    }
}

