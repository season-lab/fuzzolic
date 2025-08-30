use anyhow::Result;
use fuzzolic_solver::{Config, SMTSolver};
use log::{info, warn, error};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};
use std::thread;

static SHUTDOWN: AtomicBool = AtomicBool::new(false);
static GO_SIGNAL: AtomicBool = AtomicBool::new(false);

fn setup_signal_handlers() -> Result<()> {
    // Handle SIGINT (Ctrl+C) and SIGTERM
    ctrlc::set_handler(move || {
        info!("Received shutdown signal, cleaning up...");
        SHUTDOWN.store(true, Ordering::SeqCst);
    })?;
    
    // Set up additional signal handlers for Unix systems
    #[cfg(unix)]
    {
        use nix::sys::signal::{self, Signal, SigHandler};
        
        // SIGUSR1 handler - sets go signal (tracer ready)
        extern "C" fn handle_usr1(_: i32) {
            GO_SIGNAL.store(true, Ordering::SeqCst);
        }
        
        // SIGUSR2 handler - immediate shutdown with cleanup
        extern "C" fn handle_usr2(_: i32) {
            eprintln!("[SOLVER] Received SIGUSR2");
            SHUTDOWN.store(true, Ordering::SeqCst);
        }
        
        // SIGSEGV handler - crash with cleanup
        extern "C" fn handle_segfault(_: i32) {
            eprintln!("[SOLVER] Received SIGSEGV");
            SHUTDOWN.store(true, Ordering::SeqCst);
            std::process::exit(139); // SIGSEGV exit code
        }
        
        // Install signal handlers
        unsafe {
            if let Err(e) = signal::signal(Signal::SIGUSR1, SigHandler::Handler(handle_usr1)) {
                warn!("Failed to install SIGUSR1 handler: {}", e);
            }
            if let Err(e) = signal::signal(Signal::SIGUSR2, SigHandler::Handler(handle_usr2)) {
                warn!("Failed to install SIGUSR2 handler: {}", e);
            }
            if let Err(e) = signal::signal(Signal::SIGTERM, SigHandler::Handler(handle_usr2)) {
                warn!("Failed to install SIGTERM handler: {}", e);
            }
            if let Err(e) = signal::signal(Signal::SIGSEGV, SigHandler::Handler(handle_segfault)) {
                warn!("Failed to install SIGSEGV handler: {}", e);
            }
        }
    }
    
    Ok(())
}

fn main() -> Result<()> {
    // Initialize logging
    env_logger::init();
    
    info!("Starting Fuzzolic SMT Solver");
    
    // Parse command line arguments
    let config = Config::parse_with_env()?;
    info!("Configuration loaded: {:?}", config);
    
    // Set up signal handlers
    if let Err(e) = setup_signal_handlers() {
        warn!("Failed to setup signal handlers: {}", e);
    }
    
    // Initialize solver
    let mut solver = SMTSolver::new(&config)?;
    info!("SMT Solver initialized successfully");
    
    // Load initial testcase if provided
    if let Err(e) = solver.load_initial_testcase() {
        warn!("Failed to load initial testcase: {}", e);
    }
    
    // Print solver configuration
    info!("Shared memory keys - expr_pool: {}, query: {}, bitmap: {:?}", 
          config.expr_pool_shm_key, config.query_shm_key, config.bitmap_shm_key);
    
    // Wait for tracer initialization (SIGUSR1 signal)
    info!("Waiting for tracer initialization...");
    
    let polling_interval = Duration::from_millis(5); // 5ms polling
    let start_time = Instant::now();
    
    loop {
        if SHUTDOWN.load(Ordering::SeqCst) {
            info!("Shutdown signal received during initialization");
            break;
        }
        
        // Check if tracer sent SIGUSR1 (go signal)
        if GO_SIGNAL.load(Ordering::SeqCst) {
            info!("Received tracer ready signal (SIGUSR1)");
            break;
        }
        
        // Check for timeout (optional)
        if let Some(timeout_ms) = config.timeout {
            if start_time.elapsed().as_millis() > timeout_ms as u128 {
                warn!("Timeout waiting for tracer initialization");
                break;
            }
        }
        
        std::thread::sleep(polling_interval);
    }

    // Main processing loop
    loop {
        // Check for shutdown signal
        if SHUTDOWN.load(Ordering::SeqCst) {
            info!("Shutdown signal received, exiting...");
            break;
        }
        
        // Check timeout if configured
        if let Some(timeout) = config.timeout {
            if timeout > 0 {
                let elapsed = start_time.elapsed().as_millis() as u64;
                if elapsed > timeout {
                    info!("Timeout reached ({}ms), exiting...", timeout);
                    break;
                }
            }
        }
        
        // Process queries from shared memory
        match solver.process_shared_queries() {
            Ok(queries_processed) => {
                if queries_processed > 0 {
                    info!("Processed {} queries", queries_processed);
                }
                
                // If no queries processed, sleep briefly to avoid busy waiting
                if queries_processed == 0 {
                    thread::sleep(polling_interval);
                }
            }
            Err(e) => {
                // Check if this is a "no queries available" error or a real error
                if e.to_string().contains("No queries available") {
                    thread::sleep(polling_interval);
                } else {
                    error!("Error processing queries: {}", e);
                    break;
                }
            }
        }
    }
    
    // Print final statistics
    info!("Solver execution completed");
    solver.print_statistics();
    
    // Save any remaining data (bitmaps, etc.)
    if let Err(e) = solver.save_state() {
        warn!("Failed to save solver state: {}", e);
    }
    
    info!("Fuzzolic SMT Solver shutdown complete");
    Ok(())
}
