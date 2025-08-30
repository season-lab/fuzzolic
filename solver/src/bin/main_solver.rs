use anyhow::Result;
use fuzzolic_solver::{Config, run_solver};
use log::info;

fn main() -> Result<()> {
    // Initialize logging
    env_logger::init();
    
    // Parse command line arguments
    let config = Config::parse_with_env()?;
    info!("Starting Fuzzolic main solver with config: {:?}", config);
    
    // Run the solver with fuzzy solver disabled by default
    // This uses the existing production solver implementation
    run_solver(config, false)?;
    
    info!("Main solver completed successfully");
    Ok(())
}
