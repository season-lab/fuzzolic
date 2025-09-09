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
    let z3_expr = SMTSolver::translate_expression_static(ctx, expr)?;
    let solver_z3 = z3::Solver::new(ctx);
    let as_bool = z3_expr.as_bool().ok_or_else(|| anyhow::anyhow!("Dependency query expr not Bool"))?;
    solver_z3.assert(&as_bool);
    match solver_z3.check() {
        z3::SatResult::Sat => {
            debug!("Dependency query SAT");
        }
        z3::SatResult::Unsat => debug!("Dependency query UNSAT"),
        z3::SatResult::Unknown => warn!("Dependency query UNKNOWN"),
    }
    Ok(())
}
