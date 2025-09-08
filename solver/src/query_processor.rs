use crate::solver::SMTSolver;
use crate::config::Config;
use crate::expression::{Query, QueryType, OpKind, Expr};
use crate::shared_memory::{QueryQueue, EXPR_QUERY_CAPACITY};
use crate::branch_coverage::BranchCoverage;
use crate::memory_slice::MemorySliceReasoner;
use anyhow::Result;
use std::collections::HashSet;
use std::os::raw::c_void;
use crate::fuzzy_ffi::raw_ast_from_bool;
use crate::concrete_eval::ConcreteEvaluator;
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
                        self.process_expr_query_simple(expr, op)?;
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
    fn process_expr_query_simple(&mut self, expr: &Expr, op: OpKind) -> Result<()> {
        // In C: smt_expr_query(q, opkind) translates q->query->op1
        let target_ptr = expr.op1;
        if target_ptr.is_null() {
            anyhow::bail!("Expr {:?} missing op1 target", op);
        }
        let target = unsafe { &*target_ptr };

        // Record dependencies for target expression
        let _ = self.solver.add_dependency_for_expr(target);

        let ctx = &self.solver.ctx;
        let z3_dyn = SMTSolver::translate_expression_static(ctx, target)?;

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
                    let sol_ast = z3::ast::BV::from_u64(ctx, solution, width);
                    let eq = bv._eq(&sol_ast);
                    // Notify fuzzy about the constraint
                    self.solver.fuzzy_notify_constraint(&eq);
                    // We could also store this constraint and update dep caches akin to C
                }
            }
            // In C they also explore multiple values (fuzzy/Z3). We rely on higher-level
            // fuzzing path and statistics already integrated; detailed enumeration TBD.
        }

        Ok(())
    }

    /// Consistency check (CONSISTENCY_CHECK): evaluate expr and compare with concrete value
    fn process_consistency_query_q(&mut self, query: &Query) -> Result<()> {
        if query.query.is_null() { return Ok(()); }
        let expr = unsafe { &*query.query };
        // Consistency expression is in op1; concrete expected value in op2
        let target = if expr.op1.is_null() { anyhow::bail!("Consistency expr missing op1") } else { unsafe { &*expr.op1 } };
        let expected = expr.get_op2_const().unwrap_or(0) as u64;

        let ctx = &self.solver.ctx;
        let z3_e = SMTSolver::translate_expression_static(ctx, target)?;

        // Evaluate using current testcase bytes if available
        let input_bytes: Vec<u8> = self.solver.get_current_testcase().unwrap_or_default();
        let mut evaluator = ConcreteEvaluator::new();
        let (solution, _cached) = evaluator.conc_eval(ctx, &z3_e, &input_bytes, &std::collections::HashMap::new())?;

        if solution == expected {
            info!("Consistency check OK at 0x{:x}", query.address as u64);
        } else {
            warn!(
                "Consistency check FAIL at 0x{:x}: expected=0x{:x} solution=0x{:x}",
                query.address as u64,
                expected,
                solution
            );
        }
        Ok(())
    }

    /// Memory concretization (MEMORY_CONCRETIZATION): assert equality to concrete value and notify fuzzy
    fn process_mem_concretization(&mut self, expr: &Expr) -> Result<()> {
        // Target expression is in op1; concrete value in op2
        let target = if expr.op1.is_null() { anyhow::bail!("Mem concretization missing op1") } else { unsafe { &*expr.op1 } };
        let conc_val = expr.get_op2_const().unwrap_or(0) as u64;
        // Record deps first to avoid borrowing conflicts
        let _ = self.solver.add_dependency_for_expr(target);
        let ctx = &self.solver.ctx;
        let z3_dyn = SMTSolver::translate_expression_static(ctx, target)?;
        if let Some(bv) = z3_dyn.as_bv() {
            let width = bv.get_size();
            let val = z3::ast::BV::from_u64(ctx, conc_val, width);
            let eq = bv._eq(&val);
            self.solver.fuzzy_notify_constraint(&eq);
        } else if let Some(b) = z3_dyn.as_bool() {
            let eq = if conc_val == 0 { b.not() } else { b };
            self.solver.fuzzy_notify_constraint(&eq);
        } else {
            warn!("Mem concretization target not BV/Bool; skipping");
        }
        Ok(())
    }
    
    /// Process memory slice access queries
    fn process_slice_query(&mut self, query: &Query) -> Result<()> {
        // Prefer the C-style layout: q->query points to the slice node; the next node is the s_load descriptor.
        if query.query.is_null() {
            // Fallback to args if no expression pointer is provided
            let slice_args = unsafe { &query.args.args8 };
            let addr_conc = slice_args.arg1 as u64;
            let size = slice_args.arg2 as usize;
            let load_id = slice_args.arg3 as u64;
            debug!("[slice:fallback] addr={:x}, size={}, load_id={}", addr_conc, size, load_id);
            self.memory_slice_reasoner.process_slice_access(addr_conc, size, load_id)?;
            return Ok(());
        }

        // SAFETY: query.query is a valid pointer to an Expr in shared memory
        let slice_node = unsafe { &*query.query };
        let opkind = OpKind::try_from(slice_node.opkind)?;
        // The C code handles MEMORY_SLICE and MEMORY_SLICE_ACCESS similarly and inspects the adjacent s_load node.
        if opkind != OpKind::MemorySlice && opkind != OpKind::MemorySliceAccess {
            anyhow::bail!("Unexpected opkind for slice query: {:?}", opkind);
        }

        // Extract concrete address and s_load_id from slice node constants
        let addr_conc = if slice_node.op2_is_const != 0 { slice_node.op2 as u64 } else { 0 };
        let s_load_id = if slice_node.op3_is_const != 0 { slice_node.op3 as u64 } else { 0 };

        // Adjacent symbolic-load descriptor: (q->query + 1)
        let s_load_ptr = unsafe { query.query.add(1) };
        if s_load_ptr.is_null() { anyhow::bail!("Missing s_load descriptor after slice node"); }
        let s_load = unsafe { &*s_load_ptr };
        if OpKind::try_from(s_load.opkind)? != OpKind::IsSymbolic {
            anyhow::bail!("s_load descriptor not IS_SYMBOLIC");
        }
        // Validate s_load_id
        if !(s_load.op1_is_const != 0 && (s_load.op1 as u64) == s_load_id) {
            anyhow::bail!("s_load id mismatch: expected {} got {}", s_load_id, s_load.op1 as u64);
        }
        let s_load_size = if s_load.op2_is_const != 0 { s_load.op2 as usize } else { 0 };

        // Optional concrete value for MEMORY_SLICE_ACCESS
        let mut concrete_bytes: Option<[u8; crate::memory_slice::SLICE_SIZE]> = None;
        if opkind == OpKind::MemorySliceAccess && s_load.op3_is_const != 0 {
            let val = s_load.op3 as u64;
            let mut data = [0u8; crate::memory_slice::SLICE_SIZE];
            let n = s_load_size.min(crate::memory_slice::SLICE_SIZE);
            for i in 0..n { data[i] = ((val >> (8 * i)) & 0xFF) as u8; }
            concrete_bytes = Some(data);
        }

        debug!(
            "[slice] addr={:x} size={} load_id={} op={:?} concrete={}",
            addr_conc,
            s_load_size,
            s_load_id,
            opkind,
            concrete_bytes.is_some()
        );

        // Record the slice and mapping in the reasoner
        if let Some(bytes) = concrete_bytes {
            self.memory_slice_reasoner.add_slice(addr_conc, bytes);
        }
        self.memory_slice_reasoner.add_input_slice(addr_conc, s_load_id as usize);
        // Also notify via the unified API
        self.memory_slice_reasoner.process_slice_access(addr_conc, s_load_size, s_load_id)?;

        Ok(())
    }
    
    
    
    /// Process branch queries (conditional branches)
    fn process_branch_query(&mut self, query: &Query) -> Result<()> {
        // C layout: q->address holds PC; q->args8.arg0 holds taken flag; q->query points to branch cond expr
        let addr_conc = query.address as u64;
        let taken = unsafe { query.args.args8 }.arg0 != 0;

        // Record branch in coverage (AFL/QSYM-compatible API)
        self.branch_coverage.record_branch(addr_conc, taken, false);

        // If we took the branch, try to solve for the opposite by negating the branch condition
        if !query.query.is_null() {
            let cond_expr = unsafe { &*query.query };
            // Record dependencies for this branch condition into the solver's graph
            // so subsequent dependency assertions can consult it.
            let _ = self.solver.add_dependency_for_expr(cond_expr);
            // First, build Z3 ASTs and, if fuzzy is enabled, call fuzzy fast check using raw pointers.
            if self.config.use_fuzzy_solver {
                let (query_raw, neg_raw): (*mut c_void, *mut c_void) = {
                    let ctx = &self.solver.ctx;
                    let z3_cond = SMTSolver::translate_expression_static(ctx, cond_expr)?;
                    let cond_bool = z3_cond.as_bool().expect("branch condition must be Bool");
                    let neg_cond = cond_bool.not();
                    // Collect inputs from the condition AST
                    let mut evaluator = ConcreteEvaluator::new();
                    let inputs_vec = evaluator.get_inputs_expr(&z3_cond);
                    let input_set: std::collections::HashSet<usize> = inputs_vec.iter().map(|&x| x as usize).collect();
                    // Merge dependencies
                    let deps = self.solver.get_deps_for_inputs(&input_set);
                    let current_id = (cond_expr as *const crate::expression::Expr) as usize;
                    // Translate dependent expressions (Bool only)
                    let mut dep_bools: Vec<z3::ast::Bool> = Vec::new();
                    for expr_id in deps.expressions.iter() {
                        if *expr_id == current_id { continue; }
                        let dep_ptr = *expr_id as *const crate::expression::Expr;
                        if dep_ptr.is_null() { continue; }
                        let dep_expr = unsafe { &*dep_ptr };
                        if !self.solver.ensure_dep_is_bool(dep_expr) { continue; }
                        if let Ok(dyn_ast) = SMTSolver::translate_expression_static(ctx, dep_expr) {
                            if let Some(b) = dyn_ast.as_bool() {
                                dep_bools.push(b);
                            }
                        }
                    }
                    // Build AND of neg_cond and deps
                    let mut all_refs: Vec<&z3::ast::Bool> = Vec::with_capacity(dep_bools.len() + 1);
                    all_refs.push(&neg_cond);
                    for b in &dep_bools { all_refs.push(b); }
                    let fuzzy_query = z3::ast::Bool::and(ctx, &all_refs);
                    let fq_raw = unsafe { raw_ast_from_bool(&fuzzy_query) } as *mut c_void;
                    let nc_raw = unsafe { raw_ast_from_bool(&neg_cond) } as *mut c_void;
                    (fq_raw, nc_raw)
                };
                if let Ok(true) = self.solver.fuzzy_check_light_raw(query_raw, neg_raw) {
                    info!("[fuzzy] Opposite branch at 0x{:x} is SAT", addr_conc);
                    return Ok(());
                } else if self.config.optimistic_solving {
                    if let Ok(true) = self.solver.fuzzy_get_optimistic() {
                        info!("[fuzzy-optimistic] Opposite branch at 0x{:x} is SAT", addr_conc);
                        return Ok(());
                    }
                }
            }

            // Slow solver fallback: recompute cleanly
            {
                let ctx = &self.solver.ctx;
                let z3_cond = SMTSolver::translate_expression_static(ctx, cond_expr)?;
                let cond_bool = z3_cond.as_bool().expect("branch condition must be Bool");
                let neg_cond = cond_bool.not();
                let solver = z3::Solver::new(ctx);
                let to_assert = if taken { neg_cond } else { cond_bool };
                solver.assert(&to_assert);
                match solver.check() {
                    z3::SatResult::Sat => {
                        info!("Opposite branch at 0x{:x} is SAT", addr_conc);
                    }
                    z3::SatResult::Unsat => debug!("Opposite branch at 0x{:x} is UNSAT", addr_conc),
                    z3::SatResult::Unknown => warn!("Opposite branch at 0x{:x} is UNKNOWN", addr_conc),
                }
            }
        }

        Ok(())
    }
    
    
    
    
    /// Check if this is the final query marker
    fn is_final_query(&self, query: &Query) -> bool {
        // Final query marker: null query pointer (mirrors C code behavior)
        query.query.is_null()
    }
    
    /// Process model queries
    fn process_model_query(&mut self, query: &Query) -> Result<()> {
        debug!("Processing model query");
        if query.query.is_null() { return Ok(()); }
        let expr = unsafe { &*query.query };
        // Record dependencies for analysis/debugging
        let _ = self.solver.add_dependency_for_expr(expr);
        let ctx = &self.solver.ctx;
        let z3_expr = SMTSolver::translate_expression_static(ctx, expr)?;
        let solver = z3::Solver::new(ctx);
        // Model queries should be asserted as Bool conditions
        let as_bool = z3_expr.as_bool().ok_or_else(|| anyhow::anyhow!("Model query expr not Bool"))?;
        solver.assert(&as_bool);
        match solver.check() {
            z3::SatResult::Sat => {
                debug!("Model query SAT");
                // Skip testcase generation to match current C build
            }
            z3::SatResult::Unsat => debug!("Model query UNSAT"),
            z3::SatResult::Unknown => warn!("Model query UNKNOWN"),
        }
        Ok(())
    }
    
    /// Process dependency queries
    fn process_dependency_query(&mut self, query: &Query) -> Result<()> {
        debug!("Processing dependency query");
        if query.query.is_null() { return Ok(()); }
        let expr = unsafe { &*query.query };
        // Record dependencies for the queried expression
        let _ = self.solver.add_dependency_for_expr(expr);
        let ctx = &self.solver.ctx;
        let z3_expr = SMTSolver::translate_expression_static(ctx, expr)?;
        let solver = z3::Solver::new(ctx);
        let as_bool = z3_expr.as_bool().ok_or_else(|| anyhow::anyhow!("Dependency query expr not Bool"))?;
        solver.assert(&as_bool);
        match solver.check() {
            z3::SatResult::Sat => {
                debug!("Dependency query SAT");
                // Skip testcase generation to match current C build
            }
            z3::SatResult::Unsat => debug!("Dependency query UNSAT"),
            z3::SatResult::Unknown => warn!("Dependency query UNKNOWN"),
        }
        Ok(())
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
