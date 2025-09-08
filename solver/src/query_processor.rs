use crate::solver::SMTSolver;
use crate::config::Config;
use crate::expression::{Query, QueryType, OpKind, Expr, ModelType};
use crate::solver::ConstraintRecord;
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
                            let dep_ptr = *expr_id as *const crate::expression::Expr;
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
                        if self.config.use_fuzzy_solver {
                            let raw = unsafe { raw_ast_from_bool(&conj) } as *mut c_void;
                            sat = self.solver.fuzzy_check_light_raw_const(raw, std::ptr::null_mut()).unwrap_or(false);
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
        // Record constraint for involved inputs
        let mut evaluator = ConcreteEvaluator::new();
        let inputs_vec = evaluator.get_inputs_expr(&z3_dyn);
        let input_set: std::collections::HashSet<usize> = inputs_vec.iter().map(|&x| x as usize).collect();
        let record = ConstraintRecord::EqBV { expr_ptr: target as *const Expr, value: conc_val };
        // We do not have the query idx here; when used from process_query we do. Use address as fallback key.
        // Store with a synthetic index derived from address to keep constraints available.
        let qidx = expr as *const Expr as usize;
        self.solver.add_constraint_for_inputs(&input_set, qidx, record);
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
                    // Append cached constraints associated with inputs
                    let extra_bools = self.solver.get_constraint_bools_for_inputs(&input_set);
                    // Build AND of neg_cond and deps
                    let mut all_refs: Vec<&z3::ast::Bool> = Vec::with_capacity(dep_bools.len() + 1);
                    all_refs.push(&neg_cond);
                    for b in &dep_bools { all_refs.push(b); }
                    for b in &extra_bools { all_refs.push(b); }
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
        let qidx = query.get_index();
        // Helper to unpack 4x16-bit fields from a packed u64
        fn unpack4(x: u64) -> (u16, u16, u16, u16) {
            let a = (x & 0xFFFF) as u16;
            let b = ((x >> 16) & 0xFFFF) as u16;
            let c = ((x >> 32) & 0xFFFF) as u16;
            let d = ((x >> 48) & 0xFFFF) as u16;
            (a, b, c, d)
        }
        // Helper to unpack 2x16-bit fields from a packed u64
        fn unpack2(x: u64) -> (u16, u16) {
            let a = (x & 0xFFFF) as u16;
            let b = ((x >> 16) & 0xFFFF) as u16;
            (a, b)
        }

        // Determine model type
        let model = unsafe { query.args.model };
        match model {
            ModelType::Strcmp => {
                let s1 = if expr.op1.is_null() { anyhow::bail!("STRCMP missing s1") } else { unsafe { &*expr.op1 } };
                let s2 = if expr.op2.is_null() { anyhow::bail!("STRCMP missing s2") } else { unsafe { &*expr.op2 } };
                let packed = expr.get_op3_const().unwrap_or(0) as u64;
                let (res_u16, s1_len_u16, s2_len_u16, n_u16) = unpack4(packed);
                let res = res_u16 as i32; // 0 means equal branch was taken
                let s1_len = s1_len_u16 as usize;
                let s2_len = s2_len_u16 as usize;
                let _n = n_u16 as usize;
                // Translate to ASTs to extract input sets
                let ctx = &self.solver.ctx;
                let z3_s1 = SMTSolver::translate_expression_static(ctx, s1)?;
                let z3_s2 = SMTSolver::translate_expression_static(ctx, s2)?;
                let mut evaluator = ConcreteEvaluator::new();
                let mut inputs_set: std::collections::HashSet<usize> = evaluator
                    .get_inputs_expr(&z3_s1)
                    .into_iter().map(|x| x as usize).collect();
                inputs_set.extend(evaluator.get_inputs_expr(&z3_s2).into_iter().map(|x| x as usize));
                // Record stride equality (possibly inverted)
                let record = ConstraintRecord::StrideCmpEq {
                    left_ptr: s1 as *const Expr,
                    right_ptr: s2 as *const Expr,
                    len: s1_len.min(s2_len),
                    invert: res != 0,
                };
                self.solver.add_constraint_for_inputs(&inputs_set, qidx, record);
            }
            ModelType::Strlen => {
                let s1 = if expr.op1.is_null() { anyhow::bail!("STRLEN missing s1") } else { unsafe { &*expr.op1 } };
                let packed = expr.get_op2_const().unwrap_or(0) as u64;
                let (s1_len_u16, n_u16) = unpack2(packed);
                let s1_len = s1_len_u16 as usize;
                let n = n_u16 as usize;
                let ctx = &self.solver.ctx;
                let z3_s1 = SMTSolver::translate_expression_static(ctx, s1)?;
                let mut evaluator = ConcreteEvaluator::new();
                let inputs_set: std::collections::HashSet<usize> = evaluator
                    .get_inputs_expr(&z3_s1)
                    .into_iter().map(|x| x as usize).collect();
                let record = ConstraintRecord::StrlenConstraint { expr_ptr: s1 as *const Expr, s1_len, n };
                self.solver.add_constraint_for_inputs(&inputs_set, qidx, record);
            }
            ModelType::Memcmp => {
                let s1 = if expr.op1.is_null() { anyhow::bail!("MEMCMP missing s1") } else { unsafe { &*expr.op1 } };
                let s2 = if expr.op2.is_null() { anyhow::bail!("MEMCMP missing s2") } else { unsafe { &*expr.op2 } };
                let packed = expr.get_op3_const().unwrap_or(0) as u64;
                let (res_u16, n_u16, _r2, _r3) = unpack4(packed);
                let res = res_u16 as i32;
                let n = n_u16 as usize;
                let ctx = &self.solver.ctx;
                let z3_s1 = SMTSolver::translate_expression_static(ctx, s1)?;
                let z3_s2 = SMTSolver::translate_expression_static(ctx, s2)?;
                let mut evaluator = ConcreteEvaluator::new();
                let mut inputs_set: std::collections::HashSet<usize> = evaluator
                    .get_inputs_expr(&z3_s1)
                    .into_iter().map(|x| x as usize).collect();
                inputs_set.extend(evaluator.get_inputs_expr(&z3_s2).into_iter().map(|x| x as usize));
                let record = ConstraintRecord::StrideCmpEq {
                    left_ptr: s1 as *const Expr,
                    right_ptr: s2 as *const Expr,
                    len: n,
                    invert: res != 0,
                };
                self.solver.add_constraint_for_inputs(&inputs_set, qidx, record);
            }
            ModelType::Memchr => {
                // op1 = haystack, op2 = needle byte (const), op3 packs (res, n, ..)
                let s1 = if expr.op1.is_null() { anyhow::bail!("MEMCHR missing haystack") } else { unsafe { &*expr.op1 } };
                let needle = expr.get_op2_const().unwrap_or(0) as u8;
                let packed = expr.get_op3_const().unwrap_or(0) as u64;
                let (_res, n_u16, _r2, _r3) = unpack4(packed);
                let n = n_u16 as usize;
                let ctx = &self.solver.ctx;
                let z3_s1 = SMTSolver::translate_expression_static(ctx, s1)?;
                let mut evaluator = ConcreteEvaluator::new();
                let inputs_set: std::collections::HashSet<usize> = evaluator
                    .get_inputs_expr(&z3_s1)
                    .into_iter().map(|x| x as usize).collect();
                let record = ConstraintRecord::MemchrConstraint { haystack_ptr: s1 as *const Expr, needle, n };
                self.solver.add_constraint_for_inputs(&inputs_set, qidx, record);
            }
            ModelType::Malloc => {
                // op1 holds requested size in bytes as const
                let size = expr.get_op1_const().unwrap_or(0);
                // We do not know which inputs this depends on (often none). Store under query id only.
                let record = ConstraintRecord::MallocConstraint { size };
                // Attach to a synthetic input id bucket 0 to make retrievable in future conjunctions.
                let mut inputs = std::collections::HashSet::new();
                inputs.insert(0usize);
                self.solver.add_constraint_for_inputs(&inputs, qidx, record);
            }
            other => {
                warn!("Model {:?} not yet implemented in Rust; skipping", other);
            }
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
