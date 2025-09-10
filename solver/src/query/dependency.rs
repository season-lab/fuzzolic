use anyhow::Result;
use log::{debug, warn};
use crate::expressions::expression::Query;
use crate::solver::SMTSolver;

pub fn handle_dependency(solver: &mut SMTSolver, query: &Query) -> Result<()> {
    debug!("Processing dependency query");
    let expr = if let Some(e) = query.query_expr() { e } else { return Ok(()); };
    // Record dependencies for the queried expression
    let _ = solver.add_dependency_for_expr(expr);
    let ctx = &solver.ctx;
    let translate_start = std::time::Instant::now();
    let z3_expr = SMTSolver::translate_expression_static(ctx, expr)?;
    let translate_elapsed = translate_start.elapsed();
    solver.statistics.translation_time += translate_elapsed.as_millis() as u64;
    let solver_z3 = z3::Solver::new(ctx);
    let as_bool = z3_expr.as_bool().ok_or_else(|| anyhow::anyhow!("Dependency query expr not Bool"))?;
    solver_z3.assert(&as_bool);
    match solver_z3.check() {
        z3::SatResult::Sat => {
            debug!("Dependency query SAT");
            solver.statistics.sat_count += 1;
        }
        z3::SatResult::Unsat => {
            debug!("Dependency query UNSAT");
            solver.statistics.unsat_count += 1;
        }
        z3::SatResult::Unknown => {
            warn!("Dependency query UNKNOWN");
            solver.statistics.timeout_count += 1;
        }
    }
    Ok(())
}
