use crate::solver::SMTSolver;
use crate::utils::config::Config;
use crate::expressions::expression::{Query, QueryType, OpKind, Expr};
use crate::solver::ConstraintRecord;
use crate::shared_memory::shared_memory::{QueryQueue, EXPR_QUERY_CAPACITY};
use crate::coverage::branch_coverage::BranchCoverage;
use crate::query::memory_slice::MemorySliceReasoner;
use anyhow::Result;
use std::collections::HashSet;
use std::os::raw::c_void;
use crate::solver::concrete_eval::ConcreteEvaluator;
use log::{debug, info, warn};
use std::time::{Duration, Instant};
use z3::ast::Ast;

/// Main query processor that handles the solver loop
pub struct QueryProcessor {
    solver: SMTSolver,
    query_queue: QueryQueue,
    branch_coverage: BranchCoverage,
    memory_slice_reasoner: MemorySliceReasoner,
    config: Config,
    start_time: Instant,
    // Mirrors C-side concretization tracking
    concretized_bytes: HashSet<usize>,
    concretized_sloads: HashSet<usize>,
    addr_testcase_count: usize,
}

impl QueryProcessor {
    pub fn new(config: Config) -> Result<Self> {
        let solver = SMTSolver::new(&config)?;
        // Use configured shared memory key and capacity matching C layout
        let query_queue = QueryQueue::new(config.query_shm_key, EXPR_QUERY_CAPACITY)?;
        let branch_coverage = BranchCoverage::new(&config)?;
        
        let memory_slice_reasoner = MemorySliceReasoner::new();
        
        Ok(QueryProcessor {
            solver,
            query_queue,
            branch_coverage,
            memory_slice_reasoner,
            config: config.clone(),
            start_time: Instant::now(),
            concretized_bytes: HashSet::new(),
            concretized_sloads: HashSet::new(),
            addr_testcase_count: 0,
        })
    }

    /// Main solver loop - processes queries from shared memory
    pub fn run(&mut self, _config: &Config) -> Result<()> {
        info!("Starting query processor loop");
        
        // Initialize solver components
        self.solver.initialize()?;
        
        let _polling_interval = Duration::from_millis(_config.polling_interval_ms);
        
        loop {
            // Check for timeout
            if let Some(timeout) = self.config.timeout {
                let elapsed = self.start_time.elapsed().as_millis() as u64;
                if elapsed > timeout {
                    info!("Solver timeout reached ({}ms), exiting", timeout);
                    self.save_results()?;
                    break;
                }
            }
            
            // Try to get next query from queue
            match self.query_queue.next_query() {
                Some(query) => {
                    if self.is_final_query(&query) {
                        info!("Received final query, exiting");
                        self.save_results()?;
                        break;
                    }
                    
                    // Process the query
                    if let Err(e) = self.process_query(query) {
                        warn!("Failed to process query: {}", e);
                    }
                }
                None => {
                    // No query available, short sleep
                    std::thread::sleep(Duration::from_millis(1));
                    
                    // If no queries for too long, assume tracer crashed
                    if self.start_time.elapsed() > Duration::from_secs(30) {
                        warn!("No queries received for 30 seconds, assuming tracer crashed");
                        break;
                    }
                }
            }
        }
        
        Ok(())
    }
    
    /// Process a single query
    fn process_query(&mut self, query: Query) -> Result<()> {
        debug!("Processing query: {:?}", query.query_type);
        let start_time = Instant::now();
        
        // First mirror the C smt_query dispatch by opkind when possible
        if !query.query.is_null() {
            let expr = unsafe { &*query.query };
            if let Ok(op) = OpKind::try_from(expr.opkind) {
                match op {
                    OpKind::SymbolicPc | OpKind::SymbolicJumpTableAccess | OpKind::SymbolicLoad | OpKind::SymbolicStore => {
                        self.process_expr_query_simple(&query, expr, op)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    OpKind::MemorySliceAccess | OpKind::MemoryInputSliceAccess => {
                        self.process_slice_query(&query)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    OpKind::MemoryConcretization => {
                        self.process_mem_concretization(expr)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    OpKind::ConsistencyCheck => {
                        self.process_consistency_query_q(&query)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    OpKind::Model => {
                        self.process_model_query(&query)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    _ => {}
                }
            }
        }

        // Fallback to Rust query_type routing
        let result = match query.query_type {
            QueryType::Branch => self.process_branch_query(&query),
            QueryType::Slice => self.process_slice_query(&query),
            QueryType::Model => self.process_model_query(&query),
            QueryType::Dependency => self.process_dependency_query(&query),
        };
        
        let elapsed = start_time.elapsed();
        debug!("Query processed in {:?}", elapsed);
        
        result
    }

    /// Simple expression satisfiability query (SYMBOLIC_PC, JUMP_TABLE, LOAD/STORE)
    fn process_expr_query_simple(&mut self, query: &Query, expr: &Expr, op: OpKind) -> Result<()> {
        // In C: smt_expr_query(q, opkind) translates q->query->op1
        let target_ptr = expr.op1;
        if target_ptr.is_null() {
            anyhow::bail!("Expr {:?} missing op1 target", op);
        }
        let target = unsafe { &*target_ptr };

        // Record dependencies for target expression
        let _ = self.solver.add_dependency_for_expr(target);

        let z3_dyn = SMTSolver::translate_expression_static(&self.solver.ctx, target)?;

        // Collect inputs referenced by target expression
        let mut evaluator = ConcreteEvaluator::new();
        let input_ids_u64 = evaluator.get_inputs_expr(&z3_dyn);
        if input_ids_u64.is_empty() {
            // No inputs -> skip, as C does
            return Ok(());
        }

        // Determine if there are real inputs and if inputs are already concretized
        let mut has_real_inputs = false;
        let mut inputs_are_concretized = true;
        // If we have a current testcase, bytes < size are real; also consider sloads set
        let tc_size = self.solver.current_testcase.as_ref().map(|t| t.size()).unwrap_or(usize::MAX);
        for &id in &input_ids_u64 {
            let key = id as usize;
            if key < tc_size || !self.concretized_sloads.contains(&key) {
                has_real_inputs = true;
            }
            if !self.concretized_bytes.contains(&key) {
                inputs_are_concretized = false;
                // For LOAD/STORE, C adds missing bytes to concretized set
                if matches!(op, OpKind::SymbolicLoad | OpKind::SymbolicStore) {
                    self.concretized_bytes.insert(key);
                }
            }
        }

        if !has_real_inputs {
            // Skip as in C
            return Ok(());
        }
        if inputs_are_concretized {
            // Address likely already concretized; skip
            return Ok(());
        }

        // Optional: address reasoning guard based on solution
        let solution = expr.get_op2_const().unwrap_or(0) as u64;
        if self.config.address_reasoning && self.is_interesting_memory(solution) && self.addr_testcase_count < 1000 {
            // Minimal parity: Build an equality for LOAD/STORE and notify fuzzy engine
            if let Some(bv) = z3_dyn.as_bv() {
                if matches!(op, OpKind::SymbolicLoad | OpKind::SymbolicStore) {
                    let width = bv.get_size();
                    let sol_ast = z3::ast::BV::from_u64(&self.solver.ctx, solution, width);
                    let eq = bv._eq(&sol_ast);
                    // Notify fuzzy about the constraint
                    self.solver.fuzzy_notify_constraint(&eq);
                    // Store constraint and update dep-like caches akin to C
                    let input_set: std::collections::HashSet<usize> = input_ids_u64.iter().map(|&x| x as usize).collect();
                    let record = ConstraintRecord::EqBV { expr_ptr: target as *const Expr, value: solution };
                    let qidx = query.get_index();
                    self.solver.add_constraint_for_inputs(&input_set, qidx, record);

                    // Bounded enumeration of alternative solutions
                    // Strategy: ask fuzzy fast-check on (expr == alt) for several alt guesses derived
                    // from toggling low bits. If fuzzy is disabled, fall back to a quick Z3 check.
                    let mut tried = 0usize;
                    let max_try = self.config.address_enum_limit;
                    let mut alt_val = solution ^ 1; // start with 1-bit flip
                    // Drop z3_dyn to release immutable borrow of ctx before potentially mut borrowing solver
                    drop(z3_dyn);
                    while tried < max_try {
                        // Re-translate target fresh each iteration to avoid holding long borrows
                        let ctx = &self.solver.ctx;
                        let z3_t = SMTSolver::translate_expression_static(ctx, target)?;
                        let bv2 = z3_t.as_bv().expect("target must be BV");
                        let alt_ast = z3::ast::BV::from_u64(ctx, alt_val, width);
                        let alt_eq = bv2._eq(&alt_ast);
                        // Build deps and cached constraints
                        let mut evaluator = ConcreteEvaluator::new();
                        let inputs_vec = evaluator.get_inputs_expr(&z3_t);
                        let input_set: std::collections::HashSet<usize> = inputs_vec.iter().map(|&x| x as usize).collect();
                        let deps = self.solver.get_deps_for_inputs(&input_set);
                        let mut dep_bools: Vec<z3::ast::Bool> = Vec::new();
                        for expr_id in deps.expressions.iter() {
                            let dep_ptr = *expr_id as *const Expr;
                            if dep_ptr.is_null() { continue; }
                            let dep_expr = unsafe { &*dep_ptr };
                            if !self.solver.ensure_dep_is_bool(dep_expr) { continue; }
                            if let Ok(dyn_ast) = SMTSolver::translate_expression_static(ctx, dep_expr) {
                                if let Some(b) = dyn_ast.as_bool() { dep_bools.push(b); }
                            }
                        }
                        let extra_bools = self.solver.get_constraint_bools_for_inputs(&input_set);
                        // Decide SAT using fuzzy fast-check (raw AST) if enabled; fallback to Z3 otherwise
                        let mut all_refs: Vec<&z3::ast::Bool> = Vec::with_capacity(dep_bools.len() + extra_bools.len() + 1);
                        all_refs.push(&alt_eq);
                        for b in &dep_bools { all_refs.push(b); }
                        for b in &extra_bools { all_refs.push(b); }
                        let conj = z3::ast::Bool::and(ctx, &all_refs);
                        let mut sat: bool = false;
                        if self.config.use_fuzzy_solver && self.config.address_enum_use_fuzzy {
                            // Ensure the AST stays alive during the FFI call
                            let (ctx_raw, ast_raw) = unsafe { crate::solver::fuzzy::fuzzy_ffi::inc_ref_bool(&conj) };
                            sat = self.solver
                                .fuzzy_check_light_raw_const(ast_raw as *mut c_void, std::ptr::null_mut())
                                .unwrap_or(false);
                            unsafe { crate::solver::fuzzy::fuzzy_ffi::dec_ref(ctx_raw, ast_raw) };
                        }
                        if !sat {
                            let s = z3::Solver::new(ctx);
                            s.assert(&conj);
                            sat = matches!(s.check(), z3::SatResult::Sat);
                        }
                        if sat {
                            // Rebuild alt_eq and notify; then cache the alternative constraint
                            let ctx = &self.solver.ctx;
                            let z3_t2 = SMTSolver::translate_expression_static(ctx, target)?;
                            let bv3 = z3_t2.as_bv().expect("target must be BV");
                            let alt_ast2 = z3::ast::BV::from_u64(ctx, alt_val, width);
                            let alt_eq2 = bv3._eq(&alt_ast2);
                            self.solver.fuzzy_notify_constraint(&alt_eq2);
                            // Cache using the same input set as earlier
                            let mut evaluator = ConcreteEvaluator::new();
                            let inputs_vec = evaluator.get_inputs_expr(&z3_t);
                            let input_set: std::collections::HashSet<usize> = inputs_vec.iter().map(|&x| x as usize).collect();
                            let rec = ConstraintRecord::EqBV { expr_ptr: target as *const Expr, value: alt_val };
                            self.solver.add_constraint_for_inputs(&input_set, qidx, rec);
                        }
                        tried += 1;
                        alt_val = alt_val.wrapping_add(1);
                        if alt_val == solution { alt_val = alt_val.wrapping_add(1); }
                    }
                }
            }
            // In C they also explore multiple values (fuzzy/Z3). We rely on higher-level
            // fuzzing path and statistics already integrated; detailed enumeration TBD.
        }

        Ok(())
    }

    /// Consistency check (CONSISTENCY_CHECK)
    fn process_consistency_query_q(&mut self, query: &Query) -> Result<()> {
        crate::query::mem::handle_consistency(&mut self.solver, query)
    }

    /// Memory concretization (MEMORY_CONCRETIZATION): assert equality to concrete value and notify fuzzy
    fn process_mem_concretization(&mut self, expr: &Expr) -> Result<()> {
        crate::query::mem::handle_mem_concretization(&mut self.solver, expr)
    }
    
    /// Process memory slice access queries
    fn process_slice_query(&mut self, query: &Query) -> Result<()> {
        crate::query::mem::handle_slice(&mut self.solver, &mut self.memory_slice_reasoner, &self.config, query)
    }
    
    
    
    /// Process branch queries (conditional branches)
    fn process_branch_query(&mut self, query: &Query) -> Result<()> {
        crate::query::branch::handle_branch(&mut self.solver, &mut self.branch_coverage, &self.config, query)
    }
    
    
    
    
    /// Check if this is the final query marker
    fn is_final_query(&self, query: &Query) -> bool {
        // Final query marker: null query pointer (mirrors C code behavior)
        query.query.is_null()
    }
    
    /// Process model queries
    fn process_model_query(&mut self, query: &Query) -> Result<()> {
        crate::query::model::handle_model(&mut self.solver, query)
    }
    
    /// Process dependency queries
    fn process_dependency_query(&mut self, query: &Query) -> Result<()> {
        crate::query::dependency::handle_dependency(&mut self.solver, query)
    }

    
    /// Save solver results and statistics
    fn save_results(&mut self) -> Result<()> {
        info!("Saving solver results");
        
        // Save branch coverage bitmaps
        self.branch_coverage.save_bitmaps()?;
        
        // Print statistics
        self.solver.print_statistics();
        info!("Solver statistics:");
        // Statistics already printed by print_statistics()
        
        Ok(())
    }

    /// Heuristic for interesting memory (placeholder for C's is_interesting_memory)
    fn is_interesting_memory(&self, addr: u64) -> bool {
        addr != 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_query_processor_creation() {
        let _ = Config {
            testcase_path: Some("test.dat".into()),
            output_dir: Some("/tmp/output".into()),
            timeout: Some(5000),
            ..Default::default()
        };
        
        // This test would require proper shared memory setup
        // let processor = QueryProcessor::new(config);
        // assert!(processor.is_ok());
    }
}
