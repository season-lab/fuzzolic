use crate::solver::SMTSolver;
use crate::config::Config;
use crate::expression::{Expr, Query, QueryType};
use crate::shared_memory::QueryQueue;
use crate::branch_coverage::BranchCoverage;
use crate::memory_slice::MemorySliceReasoner;
use crate::concrete_eval::ConcreteEvaluator;
use anyhow::Result;
use log::{debug, info, warn};
use std::time::{Duration, Instant};

/// Main query processor that handles the solver loop
pub struct QueryProcessor {
    solver: SMTSolver,
    query_queue: QueryQueue,
    branch_coverage: BranchCoverage,
    memory_slice_reasoner: MemorySliceReasoner,
    config: Config,
    start_time: Instant,
}

impl QueryProcessor {
    pub fn new(config: Config) -> Result<Self> {
        let solver = SMTSolver::new(&config)?;
        let query_queue = QueryQueue::new(0x1234, 1000)?; // Default shared memory key
        let branch_coverage = BranchCoverage::new(&config)?;
        
        let memory_slice_reasoner = MemorySliceReasoner::new();
        
        Ok(QueryProcessor {
            solver,
            query_queue,
            branch_coverage,
            memory_slice_reasoner,
            config: config.clone(),
            start_time: Instant::now(),
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
    
    /// Process memory slice access queries
    fn process_slice_query(&mut self, query: &Query) -> Result<()> {
        let slice_args = unsafe { &query.args.args8 };
        let addr_conc = slice_args.arg1 as u64;
        let size = slice_args.arg2 as usize;
        let load_id = slice_args.arg3 as u64;
        
        debug!("Processing slice query: addr={:x}, size={}, load_id={}", addr_conc, size, load_id);
        
        // Use memory slice reasoner to handle the query
        self.memory_slice_reasoner.process_slice_access(addr_conc, size, load_id)?;
        
        Ok(())
    }
    
    #[allow(dead_code)]
    pub fn process_input_slice_query(&mut self, _config: &Config) -> Result<()> {
        debug!("Processing input slice query");
        
        // This would handle symbolic input reasoning
        
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
            let ctx = &self.solver.ctx;
            let z3_cond = SMTSolver::translate_expression_static(ctx, cond_expr)?;
            let solver = z3::Solver::new(ctx);
            // In C: if taken => assert(not cond); else assert(cond)
            let cond_bool = z3_cond.as_bool().expect("branch condition must be Bool");
            let to_assert = if taken { cond_bool.not() } else { cond_bool };
            solver.assert(&to_assert);
            // Add dependency assertions (placeholder to mirror C smt_branch_query behavior)
            self.add_dependency_assertions(&ctx, &solver, cond_expr)?;
            match solver.check() {
                z3::SatResult::Sat => {
                    info!("Opposite branch at 0x{:x} is SAT", addr_conc);
                    if let Some(model) = solver.get_model() {
                        self.generate_testcase_from_model(&model, cond_expr)?;
                    }
                }
                z3::SatResult::Unsat => debug!("Opposite branch at 0x{:x} is UNSAT", addr_conc),
                z3::SatResult::Unknown => warn!("Opposite branch at 0x{:x} is UNKNOWN", addr_conc),
            }
        }

        Ok(())
    }
    
    #[allow(dead_code)]
    pub fn process_call_query(&mut self, _config: &Config) -> Result<()> {
        debug!("Processing call query");
        
        // Handle function call constraints
        // This could involve parameter constraints, return value constraints, etc.
        
        Ok(())
    }
    
    #[allow(dead_code)]
    pub fn process_expression_query(&mut self, _config: &Config) -> Result<()> {
        // This method would process expression queries if needed
        debug!("Processing expression query");
        
        // Placeholder implementation
        Ok(())
    }
    
    #[allow(dead_code)]
    fn process_expression_query_with_query(&mut self, query: &Query, _config: &Config) -> Result<()> {
        // Use the direct expression pointer from the C-compatible layout
        let expr = if query.query.is_null() { None } else { Some(unsafe { &*query.query }) };
        
        if let Some(expression) = expr {
            // Create separate context to avoid borrowing conflicts
            let ctx = z3::Context::new(&z3::Config::new());
            let z3_expr = SMTSolver::translate_expression_static(&ctx, expression)?;
            let solver = z3::Solver::new(&ctx);
            solver.assert(&z3_expr.as_bool().unwrap());
            match solver.check() {
                z3::SatResult::Sat => {
                    debug!("Expression satisfiable");
                    if let Some(model) = solver.get_model() {
                        self.generate_testcase_from_model(&model, expression)?;
                    }
                }
                z3::SatResult::Unsat => {
                    debug!("Expression unsatisfiable");
                }
                z3::SatResult::Unknown => {
                    warn!("Expression result unknown");
                }
            }
        }
        
        Ok(())
    }
    
    /// Generate testcase from Z3 model
    fn generate_testcase_from_model(&self, model: &z3::Model, _expr: &Expr) -> Result<()> {
        debug!("Generating testcase from model");
        
        // Extract input values from model
        let mut testcase_data = Vec::new();
        
        // Get current testcase size from solver
        if let Some(testcase) = self.solver.get_current_testcase() {
            testcase_data = testcase;
        } else {
            // Default testcase size
            testcase_data.resize(1024, 0);
        }
        
        // Extract values from Z3 model using eval method
        for i in 0..10 { // Iterate through potential input symbols
            let symbol_name = format!("input_{}", i);
            let symbol = z3::ast::BV::new_const(&self.solver.ctx, symbol_name.as_str(), 8);
            if let Some(value) = model.eval(&symbol, true) {
                // Convert Z3 values to bytes for testcase
                if let Some(bv_val) = value.as_u64() {
                    let val = bv_val;
                    
                    // Update testcase with new value
                    if i < testcase_data.len() {
                        testcase_data[i] = val as u8;
                    }
                }
            }
        }
        
        self.save_testcase(&testcase_data)?;
        
        Ok(())
    }
    
    /// Save generated testcase to file
    fn save_testcase(&self, data: &[u8]) -> Result<()> {
        if let Some(output_dir) = &self.config.output_dir {
            let timestamp = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_millis();
            
            let filename = format!("{}/testcase_{}.dat", output_dir.display(), timestamp);
            std::fs::write(&filename, data)?;
            
            info!("Saved testcase: {} ({} bytes)", filename, data.len());
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
        let ctx = z3::Context::new(&z3::Config::new());
        let z3_expr = SMTSolver::translate_expression_static(&ctx, expr)?;
        let solver = z3::Solver::new(&ctx);
        // Model queries should be asserted as Bool conditions
        let as_bool = z3_expr.as_bool().ok_or_else(|| anyhow::anyhow!("Model query expr not Bool"))?;
        solver.assert(&as_bool);
        match solver.check() {
            z3::SatResult::Sat => {
                debug!("Model query SAT");
                if let Some(model) = solver.get_model() {
                    self.generate_testcase_from_model(&model, expr)?;
                }
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
        let ctx = z3::Context::new(&z3::Config::new());
        let z3_expr = SMTSolver::translate_expression_static(&ctx, expr)?;
        let solver = z3::Solver::new(&ctx);
        let as_bool = z3_expr.as_bool().ok_or_else(|| anyhow::anyhow!("Dependency query expr not Bool"))?;
        solver.assert(&as_bool);
        match solver.check() {
            z3::SatResult::Sat => {
                debug!("Dependency query SAT");
                if let Some(model) = solver.get_model() {
                    self.generate_testcase_from_model(&model, expr)?;
                }
            }
            z3::SatResult::Unsat => debug!("Dependency query UNSAT"),
            z3::SatResult::Unknown => warn!("Dependency query UNKNOWN"),
        }
        Ok(())
    }

    /// Placeholder to assert dependencies alongside the branch condition
    fn add_dependency_assertions(&self, ctx: &z3::Context, solver: &z3::Solver, expr: &Expr) -> Result<()> {
        // Translate expression to Z3 again locally
        let z3_expr = SMTSolver::translate_expression_static(ctx, expr)?;

        // Collect input symbols using a temporary ConcreteEvaluator helper
        let mut evaluator = ConcreteEvaluator::new();
        let inputs = evaluator.get_inputs_expr(&z3_expr);
        debug!("Dependency assertion: collected {} input(s): {:?}", inputs.len(), inputs);

        // Map input list to a set for dependency graph query
        let mut input_set: std::collections::HashSet<usize> = std::collections::HashSet::new();
        for id in inputs.iter() { input_set.insert(*id as usize); }

        // Retrieve merged dependencies for these inputs
        let deps = self.solver.get_deps_for_inputs(&input_set);
        debug!(
            "Merged dependency: inputs={:?} expressions={:?}",
            deps.inputs, deps.expressions
        );

        // Per-call cache to avoid retranslating the same dependency expressions
        // Keyed by raw pointer value (usize) of the expression.
        let mut dep_bool_cache: std::collections::HashMap<usize, Option<z3::ast::Bool>> =
            std::collections::HashMap::new();

        // Assert each dependent expression as a prerequisite constraint.
        // Expressions are stored in the graph by their raw pointer value (usize).
        let current_id = (expr as *const Expr) as usize;
        for expr_id in deps.expressions.iter() {
            // Mirror C's add_deps_to_solver(..., skip_expr): do not assert the
            // current expression among its own prerequisites.
            if *expr_id == current_id { continue; }

            // Try cache first
            let cached = dep_bool_cache.get(expr_id).cloned();
            let maybe_bool = if let Some(cached_opt) = cached {
                cached_opt
            } else {
                // Translate and cache
                let dep_expr_ptr = *expr_id as *const Expr;
                if dep_expr_ptr.is_null() {
                    dep_bool_cache.insert(*expr_id, None);
                    None
                } else {
                    let dep_expr = unsafe { &*dep_expr_ptr };
                    match SMTSolver::translate_expression_static(ctx, dep_expr) {
                        Ok(z3_dep) => {
                            let as_bool = z3_dep.as_bool().cloned();
                            dep_bool_cache.insert(*expr_id, as_bool.clone());
                            as_bool
                        }
                        Err(e) => {
                            debug!("Failed to translate dependency expr id={} err={}", expr_id, e);
                            dep_bool_cache.insert(*expr_id, None);
                            None
                        }
                    }
                }
            };

            if let Some(as_bool) = maybe_bool {
                solver.assert(&as_bool);
            } else {
                // Non-bool or failed translation: skip.
                debug!("Skipping non-bool/failed dependency expr id={}", expr_id);
            }
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
