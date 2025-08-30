pub mod branch_coverage;
pub mod config;
pub mod dependency;
pub mod expression;
pub mod fuzzy_solver;
pub mod i386;
pub mod shared_memory;
pub mod solver;
pub mod testcase;

pub use config::Config;
pub use expression::{Expr, OpKind, Query, QueryType};
pub use testcase::Testcase;
pub use solver::{SMTSolver, SolverResult, Model};
pub use expression::SatResult;
pub use branch_coverage::BranchCoverage;
pub use shared_memory::SharedMemoryManager;
pub use fuzzy_solver::FuzzySolver;
use anyhow::Result;
use log::info;

/// Main solver runner function - production implementation
pub fn run_solver(config: Config, use_fuzzy: bool) -> Result<()> {
    info!("Starting Fuzzolic SMT solver (fuzzy: {})", use_fuzzy);
    
    // Create solver with fuzzy solver enabled based on parameter
    let mut solver_config = config.clone();
    solver_config.use_fuzzy_solver = use_fuzzy;
    
    let mut solver = SMTSolver::new(&solver_config)?;
    info!("SMT Solver initialized successfully");
    
    // Process queries from shared memory if available
    match solver.process_shared_queries() {
        Ok(queries_processed) => {
            info!("Processed {} queries from shared memory", queries_processed);
        }
        Err(e) => {
            info!("No shared memory queries available: {}", e);
        }
    }
    
    // Print final statistics
    solver.print_statistics();
    info!("Solver completed successfully");
    
    Ok(())
}
