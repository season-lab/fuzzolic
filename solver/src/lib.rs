pub mod solver;
pub mod expressions;
pub mod utils;
pub mod shared_memory;
pub mod query;
pub mod coverage;
pub mod ffi;

#[cfg(test)]
mod tests;

pub use utils::config::Config;
pub use query::processor::QueryProcessor;
// Re-export C-ABI types for header generation via cbindgen
pub use expressions::expression::{
    Expr,
    OpKind,
    Query,
    QueryArgs,
    QueryArgs8,
    QueryArgs16,
    ModelType,
};

use anyhow::Result;
use log::info;

/// Main solver runner function
pub fn run_solver(config: Config, use_fuzzy: bool) -> Result<()> {
    info!("Starting Fuzzolic SMT solver (fuzzy: {})", use_fuzzy);
    
    // Create solver with fuzzy solver enabled based on parameter
    let mut solver_config = config.clone();
    solver_config.use_fuzzy_solver = use_fuzzy;
    
    // Run the full query processing loop (C-parity behavior)
    let mut processor = QueryProcessor::new(solver_config.clone())?;
    info!("Query Processor initialized successfully");
    processor.run(&solver_config)?;
    info!("Solver completed successfully");
    
    Ok(())
}
