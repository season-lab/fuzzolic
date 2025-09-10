use crate::solver::SMTSolver;
use crate::utils::config::Config;
use crate::expressions::expression::{Query, OpKind, Expr};
use crate::solver::ConstraintRecord;
use crate::shared_memory::shared_memory::{QueryQueue, SharedExprPool, EXPR_QUERY_CAPACITY, memory_barrier, FINAL_QUERY, BranchBitmapShm};
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
    #[allow(unused)]
    expr_pool: SharedExprPool,
    #[allow(unused)]
    branch_bitmap_shm: Option<BranchBitmapShm>,
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
        // Mirror C's user-facing prints so external launcher scripts can parse keys
        println!(
            "[SOLVER] Creating shared memory #1 (key={} / 0x{:x})...",
            config.expr_pool_shm_key, config.expr_pool_shm_key
        );
        let mut expr_pool = SharedExprPool::new(
            config.expr_pool_shm_key,
            crate::shared_memory::shared_memory::EXPR_POOL_CAPACITY,
        )?;
        println!(
            "[SOLVER] Creating shared memory #2 (key={} / 0x{:x})...",
            config.query_shm_key, config.query_shm_key
        );
        let mut query_queue = QueryQueue::new(config.query_shm_key, EXPR_QUERY_CAPACITY)?;
        // Optional: branch bitmap shared memory (#3)
        let mut branch_bitmap_shm: Option<BranchBitmapShm> = None;
        if let Some(key) = config.bitmap_shm_key {
            println!(
                "[SOLVER] Creating shared memory #3 (key={} / 0x{:x})...",
                key, key
            );
            let mut bm = BranchBitmapShm::new(key)?;
            bm.clear();
            branch_bitmap_shm = Some(bm);
        }
        let branch_coverage = BranchCoverage::new(&config)?;
        
        let memory_slice_reasoner = MemorySliceReasoner::new();
        
        // Handshake sequence with tracer (mirrors C main.c)
        // 1) Clear pool and queue
        expr_pool.clear();
        query_queue.clear();
        // 2) Write SHM_READY into first slot and issue memory barrier
        query_queue.set_ready();
        memory_barrier();
        // Announce attach (C prints this right after shmat)
        println!("[SOLVER] Attached to shared memories...");
        // 3) Wait for tracer to set SHM_DONE and then skip first slot
        println!("[SOLVER] Waiting for the tracer...");
        query_queue.wait_tracer_ready_and_skip();
        memory_barrier();

        Ok(QueryProcessor {
            solver,
            query_queue,
            expr_pool,
            branch_bitmap_shm,
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
            crate::shared_memory::shared_memory::memory_barrier();
            let peek_ptr = self.query_queue.peek_current_ptr();
            debug!(
                "Queue state: read_index={} peek_ptr=0x{:x}",
                self.query_queue.get_stats().read_index,
                peek_ptr
            );
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
                    debug!("No query at index (ptr=0x{:x}); sleeping", peek_ptr);
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
        let qidx = query.get_index();
        let a8 = query.args8_copy();
        println!(
            "[SOLVER] Processing query: idx={} addr=0x{:x} expr_ptr={:?} args8=[{:#04x},{:#04x},{:#04x},{:#04x}]",
            qidx, query.address, query.query, a8.arg0, a8.arg1, a8.arg2, a8.arg3
        );
        debug!("Processing query: ptr={:?} addr=0x{:x}", query.query, query.address);
        let start_time = Instant::now();
        
        // Update statistics - increment queries processed
        self.solver.statistics.queries_processed += 1;
        debug!("Query processed, total count: {}", self.solver.statistics.queries_processed);
        
        // First mirror the C smt_query dispatch by opkind when possible
        if let Some(expr) = query.query_expr() {
            if let Ok(op) = expr.try_opkind() {
                match op {
                    OpKind::SymbolicPc | OpKind::SymbolicJumpTableAccess | OpKind::SymbolicLoad | OpKind::SymbolicStore => {
                        println!("[SOLVER] Detected simple expr query kind: {:?}", op);
                        self.process_expr_query_simple(&query, expr, op)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    OpKind::MemorySliceAccess | OpKind::MemoryInputSliceAccess => {
                        println!("[SOLVER] Detected slice access query kind: {:?}", op);
                        self.process_slice_query(&query)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    OpKind::MemoryConcretization => {
                        println!("[SOLVER] Detected memory concretization query");
                        self.process_mem_concretization(expr)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    OpKind::ConsistencyCheck => {
                        println!("[SOLVER] Detected consistency check query");
                        self.process_consistency_query_q(&query)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    OpKind::Model => {
                        println!("[SOLVER] Detected model query");
                        self.process_model_query(&query)?;
                        let elapsed = start_time.elapsed();
                        debug!("Query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    // Comparison ops -> branch condition
                    OpKind::Eq | OpKind::Ne | OpKind::Lt | OpKind::Le | OpKind::Ge | OpKind::Gt
                    | OpKind::Ltu | OpKind::Leu | OpKind::Geu | OpKind::Gtu => {
                        println!("[SOLVER] Detected branch condition: {:?}", op);
                        self.process_branch_query(&query)?;
                        let elapsed = start_time.elapsed();
                        debug!("Branch query processed in {:?}", elapsed);
                        return Ok(());
                    }
                    _ => {}
                }
                println!("[SOLVER] OpKind={:?} not explicitly handled; treating as branch", op);
            } else {
                println!("[SOLVER] Unknown OpKind byte={} — treating as branch", expr.opkind);
            }
        }

        // Fallback: default to branch processing when we cannot infer from opkind
        println!("[SOLVER] Processing as branch query (fallback)");
        let result = self.process_branch_query(&query);
        
        let elapsed = start_time.elapsed();
        debug!("Query processed in {:?}", elapsed);
        
        // Update timing statistics - use microseconds for better precision
        let elapsed_us = elapsed.as_micros() as u64;
        let elapsed_ms = (elapsed_us + 999) / 1000; // Round up to nearest millisecond
        self.solver.statistics.solving_time += elapsed_ms;
        debug!("Added {}μs ({}ms) to solving time, total: {}ms", elapsed_us, elapsed_ms, self.solver.statistics.solving_time);
        
        result
    }

    /// Simple expression satisfiability query (SYMBOLIC_PC, JUMP_TABLE, LOAD/STORE)
    fn process_expr_query_simple(&mut self, query: &Query, expr: &Expr, op: OpKind) -> Result<()> {
        // In C: smt_expr_query(q, opkind) translates q->query->op1
        let target = expr.op1_ref().ok_or_else(|| anyhow::anyhow!("Expr {:?} missing op1 target", op))?;
        println!(
            "[SOLVER] Simple expr query: kind={:?} target_ptr={:?}",
            op, target as *const Expr
        );

        // Record dependencies for target expression
        let _ = self.solver.add_dependency_for_expr(target);

        // Track translation time (including simplification) - use microseconds for better precision
        let translate_start = Instant::now();
        let z3_dyn = SMTSolver::translate_expression_static_with_stats(&self.solver.ctx, target, Some(&mut self.solver.statistics))?;
        let translate_elapsed = translate_start.elapsed();
        let translate_us = translate_elapsed.as_micros() as u64;
        let translate_ms = (translate_us + 999) / 1000; // Round up to nearest millisecond
        self.solver.statistics.translation_time += translate_ms;
        debug!("Added {}μs ({}ms) to translation time, total: {}ms", translate_us, translate_ms, self.solver.statistics.translation_time);

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
            println!("[SOLVER] Simple expr query skipped: no real inputs in target");
            // Skip as in C
            return Ok(());
        }
        if inputs_are_concretized {
            println!("[SOLVER] Simple expr query skipped: inputs already concretized");
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
                        let mut sat: bool = false;
                        let mut z3_result: Option<z3::SatResult> = None;
                        
                        // Scope the borrow to avoid conflicts
                        {
                            let extra_bools = self.solver.get_constraint_bools_for_inputs(&input_set);
                            // Decide SAT using fuzzy fast-check (raw AST) if enabled; fallback to Z3 otherwise
                            let mut all_refs: Vec<&z3::ast::Bool> = Vec::with_capacity(dep_bools.len() + extra_bools.len() + 1);
                            all_refs.push(&alt_eq);
                            for b in &dep_bools { all_refs.push(b); }
                            for b in &extra_bools { all_refs.push(b); }
                            let conj = z3::ast::Bool::and(ctx, &all_refs);
                            
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
                                let result = s.check();
                                sat = matches!(result, z3::SatResult::Sat);
                                z3_result = Some(result);
                            }
                        } // extra_bools is dropped here, releasing the borrow
                        
                        // Update statistics based on Z3 result
                        if let Some(result) = z3_result {
                            match result {
                                z3::SatResult::Sat => self.solver.statistics.sat_count += 1,
                                z3::SatResult::Unsat => self.solver.statistics.unsat_count += 1,
                                z3::SatResult::Unknown => self.solver.statistics.timeout_count += 1,
                            }
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
        // Final query marker matches C constant FINAL_QUERY (0xDEAD)
        (query.query as *const std::os::raw::c_void) == FINAL_QUERY
    }
    
    /// Process model queries
    fn process_model_query(&mut self, query: &Query) -> Result<()> {
        crate::query::model::handle_model(&mut self.solver, query)
    }
    
    /// Process dependency queries
    #[allow(unused)]
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

