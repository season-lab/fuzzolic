use fuzzolic_solver::{Config, run_solver};
use anyhow::Result;
use clap::Parser;

fn main() -> Result<()> {
    env_logger::init();
    
    let config = Config::parse();
    let config = config.load_env_vars()?;
    
    run_solver(config, true)
}
