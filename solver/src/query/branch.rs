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
    let taken = unsafe { query.args.args8 }.arg0 != 0;

    branch_cov.record_branch(addr_conc, taken, false);

    if !query.query.is_null() {
        let cond_expr = unsafe { &*query.query };
        let _ = solver.add_dependency_for_expr(cond_expr);
        if config.use_fuzzy_solver {
            let (query_raw, neg_raw): (*mut c_void, *mut c_void) = {
                let ctx = &solver.ctx;
                let z3_cond = SMTSolver::translate_expression_static(ctx, cond_expr)?;
                let cond_bool = z3_cond.as_bool().expect("branch condition must be Bool");
                let neg_cond = cond_bool.not();
                let mut evaluator = ConcreteEvaluator::new();
                let inputs_vec = evaluator.get_inputs_expr(&z3_cond);
                let input_set: std::collections::HashSet<usize> = inputs_vec.iter().map(|&x| x as usize).collect();
                let deps = solver.get_deps_for_inputs(&input_set);
                let current_id = (cond_expr as *const expression::Expr) as usize;
                let mut dep_bools: Vec<z3::ast::Bool> = Vec::new();
                for expr_id in deps.expressions.iter() {
                    if *expr_id == current_id { continue; }
                    let dep_ptr = *expr_id as *const expression::Expr;
                    if dep_ptr.is_null() { continue; }
                    let dep_expr = unsafe { &*dep_ptr };
                    if !solver.ensure_dep_is_bool(dep_expr) { continue; }
                    if let Ok(dyn_ast) = SMTSolver::translate_expression_static(ctx, dep_expr) {
                        if let Some(b) = dyn_ast.as_bool() {
                            dep_bools.push(b);
                        }
                    }
                }
                let extra_bools = solver.get_constraint_bools_for_inputs(&input_set);
                let mut all_refs: Vec<&z3::ast::Bool> = Vec::with_capacity(dep_bools.len() + 1);
                all_refs.push(&neg_cond);
                for b in &dep_bools { all_refs.push(b); }
                for b in &extra_bools { all_refs.push(b); }
                let fuzzy_query = z3::ast::Bool::and(ctx, &all_refs);
                let fq_raw = unsafe { crate::solver::fuzzy::fuzzy_ffi::raw_ast_from_bool(&fuzzy_query) } as *mut c_void;
                let nc_raw = unsafe { crate::solver::fuzzy::fuzzy_ffi::raw_ast_from_bool(&neg_cond) } as *mut c_void;
                (fq_raw, nc_raw)
            };
            if let Ok(true) = solver.fuzzy_check_light_raw(query_raw, neg_raw) {
                info!("[fuzzy] Opposite branch at 0x{:x} is SAT", addr_conc);
                return Ok(());
            } else if config.optimistic_solving {
                if let Ok(true) = solver.fuzzy_get_optimistic() {
                    info!("[fuzzy-optimistic] Opposite branch at 0x{:x} is SAT", addr_conc);
                    return Ok(());
                }
            }
        }

        // Z3 fallback
        {
            let ctx = &solver.ctx;
            let z3_cond = SMTSolver::translate_expression_static(ctx, cond_expr)?;
            let cond_bool = z3_cond.as_bool().expect("branch condition must be Bool");
            let neg_cond = cond_bool.not();
            let s = z3::Solver::new(ctx);
            let to_assert = if taken { neg_cond } else { cond_bool };
            s.assert(&to_assert);
            match s.check() {
                z3::SatResult::Sat => info!("Opposite branch at 0x{:x} is SAT", addr_conc),
                z3::SatResult::Unsat => debug!("Opposite branch at 0x{:x} is UNSAT", addr_conc),
                z3::SatResult::Unknown => warn!("Opposite branch at 0x{:x} is UNKNOWN", addr_conc),
            }
        }
    }

    Ok(())
}
