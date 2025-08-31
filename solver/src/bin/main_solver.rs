use anyhow::Result;
use fuzzolic_solver::{Config, run_solver};

fn main() -> Result<()> {
    env_logger::init();
    let config = Config::parse_with_env()?;
    // Legacy binary: run in non-fuzzy mode by default
    run_solver(config, false)
}
