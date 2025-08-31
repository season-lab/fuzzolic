pub mod solver;
pub mod expression;
pub mod config;
pub mod shared_memory;
pub mod branch_coverage;
pub mod statistics;
pub mod testcase;
pub mod query_processor;
pub mod dependency_graph;
pub mod concrete_eval;
pub mod memory_slice;
pub mod fuzzy_solver;
pub mod testcase_generator;
pub mod memory_reasoning;
pub mod dependency;
pub mod z3_cache;

#[cfg(test)]
mod shared_memory_tests;
pub mod testcase_loader;
pub mod i386;
pub mod benchmarking;
pub mod expression_simplifier;

pub use config::Config;
pub use expression::{Expr, OpKind, Query, QueryType};
pub use testcase::Testcase;
pub use crate::solver::{SMTSolver, SolverStatistics};
pub use branch_coverage::BranchCoverage;
pub use shared_memory::{SharedExprPool, QueryQueue};
pub use fuzzy_solver::FuzzySolver;
pub use query_processor::QueryProcessor;
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
            info!("Processed {:?} queries from shared memory", queries_processed);
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
