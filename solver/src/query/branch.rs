use anyhow::Result;
use std::os::raw::c_void;
use log::{info, debug, warn};
use crate::expressions::expression::Query;
use crate::solver::concrete_eval::ConcreteEvaluator;
use crate::solver::SMTSolver;
use crate::coverage::branch_coverage::BranchCoverage;
use crate::utils::config::Config;
use crate::expressions::expression;

pub fn handle_branch(solver: &mut SMTSolver, branch_cov: &mut BranchCoverage, config: &Config, query: &Query) -> Result<()> {
    let addr_conc = query.address as u64;
    let taken = query.args8_copy().arg0 != 0;
    let a16 = query.args16_copy();
    println!(
        "[SOLVER] Branch query: addr=0x{:x} taken={} args16=[idx={},cnt={},idx_inv={},cnt_inv={}]",
        addr_conc, taken as u8, a16.index, a16.count, a16.index_inv, a16.count_inv
    );

    branch_cov.record_branch(addr_conc, taken, false);

    println!(
        "[SOLVER] Branch handler: raw expr_ptr={:?} (will attempt to read)",
        query.query
    );
    if let Some(cond_expr) = query.query_expr() {
        // Ensure latest writes from tracer are visible before deep traversal
        crate::shared_memory::shared_memory::memory_barrier();
        println!("[SOLVER] Branch handler: condition node acquired at ptr={:?}", cond_expr as *const crate::expressions::expression::Expr);
        // 1) Update dependency graph before solving (C parity)
        println!("[SOLVER] Branch handler: adding dependency graph entries...");
        let _ = solver.add_dependency_for_expr(cond_expr);
        println!("[SOLVER] Branch handler: dependencies added");

        // 2) Build condition + deps and solve with Z3 in an immutable scope
        {
            let ctx = &solver.ctx;
            println!("[SOLVER] Z3: translating branch condition at 0x{:x}", addr_conc);
            let z3_cond = SMTSolver::translate_expression_static(ctx, cond_expr)?;
            println!("[SOLVER] Z3: condition AST: {}", z3_cond.to_string());
            if let Some(cond_bool) = z3_cond.as_bool() {
                let neg_cond = cond_bool.not();
                // Gather input IDs from the condition and fetch dependency expressions
                let mut evaluator = ConcreteEvaluator::new();
                let inputs_vec = evaluator.get_inputs_expr(&z3_cond);
                println!("[SOLVER] Z3: inputs in condition: {:?}", inputs_vec);
                let input_set: std::collections::HashSet<usize> = inputs_vec.iter().map(|&x| x as usize).collect();
                let deps = solver.get_deps_for_inputs(&input_set);

                // Translate dependency expressions into Bool constraints
                let current_id = (cond_expr as *const expression::Expr) as usize;
                let mut dep_bools: Vec<z3::ast::Bool> = Vec::new();
                for expr_id in deps.expressions.iter() {
                    if *expr_id == current_id { continue; }
                    let dep_ptr = *expr_id as *const expression::Expr;
                    let _ = expression::Expr::with_ref_from_ptr(dep_ptr, |dep_expr| {
                        if !solver.ensure_dep_is_bool(dep_expr) { return; }
                        if let Ok(dyn_ast) = SMTSolver::translate_expression_static(ctx, dep_expr) {
                            if let Some(b) = dyn_ast.as_bool() { dep_bools.push(b); }
                        }
                    });
                }
                let s = z3::Solver::new(ctx);
                println!("[SOLVER] Z3: asserting opposite branch with {} deps (taken={})",
                         dep_bools.len(), taken);
                // Keep ASTs alive for the duration of the check and assert individually (C parity)
                let mut keep_alive: Vec<z3::ast::Bool> = Vec::with_capacity(dep_bools.len() + 2);
                let main = if taken { neg_cond.clone() } else { cond_bool.clone() };
                println!("[SOLVER] Z3: main assertion: {}", main.to_string());
                keep_alive.push(cond_bool.clone());
                keep_alive.push(neg_cond.clone());
                s.assert(&main);
                for b in &dep_bools {
                    println!("[SOLVER] Z3: dep asserted: {}", b.to_string());
                    s.assert(b);
                    keep_alive.push(b.clone());
                }

                let mut params = z3::Params::new(ctx);
                let to_ms: u32 = config.solver_timeout_ms();
                params.set_u32("timeout", to_ms);
                s.set_params(&params);
                println!("[SOLVER] Z3: timeout set to {} ms", to_ms);
                println!("[SOLVER] Z3: checking...");
                match s.check() {
                    z3::SatResult::Sat => {
                        info!("Opposite branch at 0x{:x} is SAT", addr_conc);
                        println!("[SOLVER] Opposite branch at 0x{:x} is SAT (Z3)", addr_conc);
                        branch_cov.mark_sat_branch();
                    }
                    z3::SatResult::Unsat => {
                        debug!("Opposite branch at 0x{:x} is UNSAT", addr_conc);
                        println!("[SOLVER] Opposite branch at 0x{:x} is UNSAT (Z3)", addr_conc);
                    }
                    z3::SatResult::Unknown => {
                        warn!("Opposite branch at 0x{:x} is UNKNOWN", addr_conc);
                        println!("[SOLVER] Opposite branch at 0x{:x} is UNKNOWN (Z3)", addr_conc);
                    }
                }
            } else {
                println!("[SOLVER] Z3: condition AST is not Bool — skipping Z3 check");
            }
        }
        if config.use_fuzzy_solver {
            println!("[SOLVER] fuzzy: enabled; preparing fast-check for 0x{:x}", addr_conc);
            // Build raw ASTs inside an immutable scope; rely on raw export to keep them valid
            let (query_raw, neg_raw): (*mut c_void, *mut c_void) = {
                let ctx = &solver.ctx;
                let z3_cond = SMTSolver::translate_expression_static(ctx, cond_expr)?;
                let cond_bool = z3_cond.as_bool().expect("branch condition must be Bool");
                let neg_cond = cond_bool.not();
                // Reuse dependency-building path
                let mut evaluator = ConcreteEvaluator::new();
                let inputs_vec = evaluator.get_inputs_expr(&z3_cond);
                let input_set: std::collections::HashSet<usize> = inputs_vec.iter().map(|&x| x as usize).collect();
                let deps = solver.get_deps_for_inputs(&input_set);
                let current_id = (cond_expr as *const expression::Expr) as usize;
                let mut dep_bools: Vec<z3::ast::Bool> = Vec::new();
                for expr_id in deps.expressions.iter() {
                    if *expr_id == current_id { continue; }
                    let dep_ptr = *expr_id as *const expression::Expr;
                    let _ = expression::Expr::with_ref_from_ptr(dep_ptr, |dep_expr| {
                        if !solver.ensure_dep_is_bool(dep_expr) { return; }
                        if let Ok(dyn_ast) = SMTSolver::translate_expression_static(ctx, dep_expr) {
                            if let Some(b) = dyn_ast.as_bool() { dep_bools.push(b); }
                        }
                    });
                }
                let extra_bools = solver.get_constraint_bools_for_inputs(&input_set);
                let mut all_refs: Vec<&z3::ast::Bool> = Vec::with_capacity(dep_bools.len() + 1 + extra_bools.len());
                all_refs.push(&neg_cond);
                for b in &dep_bools { all_refs.push(b); }
                for b in &extra_bools { all_refs.push(b); }
                println!("[SOLVER] fuzzy: building conjunction of {} deps + 1 neg cond (+{} cached)", dep_bools.len(), extra_bools.len());
                let fuzzy_query = z3::ast::Bool::and(ctx, &all_refs);
                let fq_raw = unsafe { crate::solver::fuzzy::fuzzy_ffi::raw_ast_from_bool(&fuzzy_query) } as *mut c_void;
                let nc_raw = unsafe { crate::solver::fuzzy::fuzzy_ffi::raw_ast_from_bool(&neg_cond) } as *mut c_void;
                (fq_raw, nc_raw)
            };
            println!("[SOLVER] fuzzy: calling check_light...");
            match solver.fuzzy_check_light_raw(query_raw, neg_raw) {
                Ok(true) => {
                    info!("[fuzzy] Opposite branch at 0x{:x} is SAT", addr_conc);
                    println!("[SOLVER] Opposite branch at 0x{:x} is SAT (fuzzy)", addr_conc);
                    // Mirror C behavior: mark SAT branch in coverage when discovered
                    branch_cov.mark_sat_branch();
                    return Ok(());
                }
                Ok(false) => {
                    println!("[SOLVER] fuzzy: fast-check returned UNSAT; continuing");
                }
                Err(e) => {
                    println!("[SOLVER] fuzzy: check_light error: {} — falling back to Z3", e);
                }
            }
            if config.optimistic_solving {
                if let Ok(true) = solver.fuzzy_get_optimistic() {
                    info!("[fuzzy-optimistic] Opposite branch at 0x{:x} is SAT", addr_conc);
                    println!("[SOLVER] Opposite branch at 0x{:x} is SAT (fuzzy-optimistic)", addr_conc);
                    branch_cov.mark_sat_branch();
                    return Ok(());
                }
            }
        } else {
            println!("[SOLVER] fuzzy: disabled; using Z3 fallback");
        }

        // (Z3 already executed above)
    } else {
        println!("[SOLVER] Branch handler: query expression pointer is NULL — skipping SAT check");
    }

    Ok(())
}
