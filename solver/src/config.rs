use clap::Parser;
use anyhow::{Result, Context};
use std::path::PathBuf;

#[derive(Parser, Debug, Clone, Default)]
#[command(name = "fuzzolic-solver")]
#[command(about = "Fuzzolic SMT solver for symbolic execution")]
pub struct Config {
    /// Path to current testcase
    #[arg(short = 'i', long)]
    pub testcase_path: Option<PathBuf>,
    
    /// Directory containing testcases
    #[arg(short = 't', long)]
    pub testcase_dir: Option<PathBuf>,
    
    /// Output directory for generated testcases
    #[arg(short = 'o', long)]
    pub output_dir: Option<PathBuf>,
    
    /// Path to branch bitmap
    #[arg(short = 'b', long)]
    pub branch_bitmap_path: Option<PathBuf>,
    
    /// Path to branch alt bitmap
    #[arg(long)]
    pub branch_alt_bitmap_path: Option<PathBuf>,
    
    /// Path to context bitmap
    #[arg(long)]
    pub context_bitmap_path: Option<PathBuf>,
    
    /// Path to branch coverage
    #[arg(long)]
    pub branch_coverage_path: Option<PathBuf>,
    
    /// Path to memory bitmap
    #[arg(short = 'm', long)]
    pub memory_bitmap_path: Option<PathBuf>,
    
    /// Enable memory slice reasoning
    #[arg(short = 's', long)]
    pub memory_slice_reasoning: bool,
    
    /// Enable address reasoning
    #[arg(short = 'a', long)]
    pub address_reasoning: bool,
    
    /// Enable optimistic solving
    #[arg(short = 'p', long)]
    pub optimistic_solving: bool,
    
    /// Expression pool shared memory key (from environment)
    #[arg(skip)]
    pub expr_pool_shm_key: u64,
    
    /// Query shared memory key (from environment)
    #[arg(skip)]
    pub query_shm_key: u64,
    
    /// Bitmap shared memory key (from environment, optional)
    #[arg(skip)]
    pub bitmap_shm_key: Option<u64>,
    
    /// Solver timeout in milliseconds
    #[arg(skip)]
    pub timeout: Option<u64>,
    
    
    /// Enable fuzzy solver
    #[arg(skip)]
    pub use_fuzzy_solver: bool,
    
    /// Polling interval in milliseconds
    #[arg(skip)]
    pub polling_interval_ms: u64,
    
    /// Enable shared memory
    #[arg(skip)]
    pub use_shared_memory: bool,
    
    /// Enable branch coverage
    #[arg(skip)]
    pub use_branch_coverage: bool,

    /// Enable expression simplifier (conservative subset)
    #[arg(skip)]
    pub use_expr_simplifier: bool,

    /// Bounded enumeration limit for address reasoning (number of alternative values to try)
    #[arg(skip)]
    pub address_enum_limit: usize,
}

impl Config {
    pub fn parse_with_env() -> Result<Self> {
        let config = Self::parse();
        config.load_env_vars()
    }
    
    pub fn load_env_vars(mut self) -> Result<Self> {
        // Parse environment variables
        self.expr_pool_shm_key = std::env::var("EXPR_POOL_SHM_KEY")
            .context("Missing EXPR_POOL_SHM_KEY environment variable")?
            .parse::<u64>()
            .context("Invalid EXPR_POOL_SHM_KEY format")?;
            
        self.query_shm_key = std::env::var("QUERY_SHM_KEY")
            .context("Missing QUERY_SHM_KEY environment variable")?
            .parse::<u64>()
            .context("Invalid QUERY_SHM_KEY format")?;
            
        // Optional environment variables
        if let Ok(bitmap_key) = std::env::var("BITMAP_SHM_KEY") {
            self.bitmap_shm_key = Some(bitmap_key.parse()
                .context("Invalid BITMAP_SHM_KEY format")?);
        }
        
        if let Ok(timeout) = std::env::var("SOLVER_TIMEOUT") {
            self.timeout = Some(timeout.parse()
                .context("Invalid SOLVER_TIMEOUT format")?);
        }
        
        if let Ok(alt_bitmap) = std::env::var("BITMAP_ALT") {
            self.branch_alt_bitmap_path = Some(PathBuf::from(alt_bitmap));
        }
        
        // Check for fuzzy solver flag
        self.use_fuzzy_solver = std::env::var("USE_FUZZY_SOLVER").unwrap_or_default() == "1";
        
        // Set default values for new fields
        self.polling_interval_ms = 10;
        self.use_shared_memory = true;
        self.use_branch_coverage = true;
        // Expression simplifier disabled by default; enable with USE_EXPR_SIMPLIFIER=1
        self.use_expr_simplifier = std::env::var("USE_EXPR_SIMPLIFIER").unwrap_or_default() == "1";
        // Address enumeration limit (bounded exploration), default 4
        self.address_enum_limit = std::env::var("ADDRESS_ENUM_LIMIT").ok()
            .and_then(|v| v.parse::<usize>().ok()).unwrap_or(4);
        
        Ok(self)
    }
    
    pub fn solver_timeout_ms(&self) -> u32 {
        self.timeout.unwrap_or(10000) as u32
    }
    
    pub fn fuzzy_timeout_ms(&self) -> u32 {
        1000 // Fixed timeout for fuzzy solver
    }
}
