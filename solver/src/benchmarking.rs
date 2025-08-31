use anyhow::Result;
use log::{debug, info, warn};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use std::fs::File;
use std::io::Write;
use serde::{Serialize, Deserialize};
use crate::expression::{Expr, SatResult};
use crate::solver::SMTSolver;
use crate::statistics::Statistics;

/// Comprehensive benchmarking and profiling system
pub struct BenchmarkSuite {
    benchmarks: Vec<Benchmark>,
    results: Vec<BenchmarkResult>,
    config: BenchmarkConfig,
    profiler: Profiler,
}

impl BenchmarkSuite {
    pub fn new(config: BenchmarkConfig) -> Self {
        Self {
            benchmarks: Vec::new(),
            results: Vec::new(),
            config,
            profiler: Profiler::new(),
        }
    }
    
    /// Add benchmark to suite
    pub fn add_benchmark(&mut self, benchmark: Benchmark) {
        self.benchmarks.push(benchmark);
    }
    
    /// Run all benchmarks
    pub fn run_all(&mut self) -> Result<BenchmarkSuiteResult> {
        info!("Starting benchmark suite with {} benchmarks", self.benchmarks.len());
        
        let suite_start = Instant::now();
        let mut suite_results = Vec::new();
        
        // Clone benchmarks to avoid borrowing issues
        let benchmarks = self.benchmarks.clone();
        
        for (i, benchmark) in benchmarks.iter().enumerate() {
            info!("Running benchmark {}/{}: {}", i + 1, benchmarks.len(), benchmark.name);
            
            let result = self.run_benchmark(benchmark)?;
            suite_results.push(result.clone());
            self.results.push(result);
            
            // Optional delay between benchmarks
            if let Some(delay) = self.config.delay_between_benchmarks {
                std::thread::sleep(delay);
            }
        }
        
        let total_time = suite_start.elapsed();
        
        let suite_result = BenchmarkSuiteResult {
            total_time,
            benchmark_count: benchmarks.len(),
            results: suite_results,
            summary: self.generate_summary(),
        };
        
        info!("Benchmark suite completed in {:?}", total_time);
        
        // Save results if configured
        if let Some(ref output_file) = self.config.output_file {
            self.save_results(output_file, &suite_result)?;
        }
        
        Ok(suite_result)
    }
    
    /// Run a single benchmark
    fn run_benchmark(&mut self, benchmark: &Benchmark) -> Result<BenchmarkResult> {
        let mut run_results = Vec::new();
        
        for run in 0..self.config.runs_per_benchmark {
            debug!("Benchmark {} run {}/{}", benchmark.name, run + 1, self.config.runs_per_benchmark);
            
            let run_result = self.run_single_benchmark_run(benchmark)?;
            run_results.push(run_result);
        }
        
        // Calculate statistics across runs
        let stats = self.calculate_run_statistics(&run_results);
        
        Ok(BenchmarkResult {
            benchmark_name: benchmark.name.clone(),
            category: benchmark.category.clone(),
            run_results,
            statistics: stats,
        })
    }
    
    /// Run a single benchmark iteration
    fn run_single_benchmark_run(&mut self, benchmark: &Benchmark) -> Result<SingleRunResult> {
        let start_time = Instant::now();
        
        // Start profiling
        self.profiler.start_profiling(&benchmark.name);
        
        // Create solver with benchmark configuration
        let mut solver = SMTSolver::new(&benchmark.solver_config)?;
        
        let mut query_results = Vec::new();
        let mut total_solve_time = Duration::ZERO;
        let mut sat_count = 0;
        let mut unsat_count = 0;
        let mut timeout_count = 0;
        
        // Process all queries in the benchmark
        for (i, query) in benchmark.queries.iter().enumerate() {
            let query_start = Instant::now();
            
            match self.execute_query(&mut solver, query, benchmark.timeout_ms) {
                Ok(result) => {
                    let query_time = query_start.elapsed();
                    total_solve_time += query_time;
                    
                    match result {
                        QueryResult::Sat => sat_count += 1,
                        QueryResult::Unsat => unsat_count += 1,
                        QueryResult::Unknown => timeout_count += 1,
                        QueryResult::Error(_) => timeout_count += 1,
                    }
                    
                    query_results.push(QueryExecutionResult {
                        query_index: i,
                        result,
                        execution_time: query_time,
                        memory_usage: self.profiler.get_current_memory_usage(),
                    });
                }
                Err(e) => {
                    warn!("Query {} failed: {}", i, e);
                    query_results.push(QueryExecutionResult {
                        query_index: i,
                        result: QueryResult::Error(e.to_string()),
                        execution_time: query_start.elapsed(),
                        memory_usage: 0,
                    });
                }
            }
        }
        
        let total_time = start_time.elapsed();
        
        // Stop profiling and get profile data
        let profile_data = self.profiler.stop_profiling(&benchmark.name);
        
        Ok(SingleRunResult {
            total_time,
            solve_time: total_solve_time,
            query_count: benchmark.queries.len(),
            sat_count,
            unsat_count,
            timeout_count,
            query_results,
            profile_data,
            solver_statistics: Statistics::default(),
        })
    }
    
    /// Execute a single query
    fn execute_query(&self, solver: &mut SMTSolver, query: &BenchmarkQuery, _timeout_ms: u32) -> Result<QueryResult> {
        match &query.query_type {
            BenchmarkQueryType::Expression(expr) => {
                // Use the available solve_query method
                match solver.solve_query(expr) {
                    Ok(sat_result) => {
                        Ok(match sat_result {
                            SatResult::Sat => QueryResult::Sat,
                            SatResult::Unsat => QueryResult::Unsat,
                            SatResult::Unknown => QueryResult::Unknown,
                        })
                    }
                    Err(e) => Ok(QueryResult::Error(e.to_string())),
                }
            }
            BenchmarkQueryType::SMTLib(_smtlib_string) => {
                // Parse and solve SMT-LIB format query
                // For now, return unknown as placeholder
                Ok(QueryResult::Unknown)
            }
            BenchmarkQueryType::Custom(_data) => {
                // Handle custom query format
                Ok(QueryResult::Unknown)
            }
        }
    }
    
    /// Calculate statistics across multiple runs
    fn calculate_run_statistics(&self, runs: &[SingleRunResult]) -> RunStatistics {
        if runs.is_empty() {
            return RunStatistics::default();
        }
        
        let total_times: Vec<f64> = runs.iter().map(|r| r.total_time.as_secs_f64()).collect();
        let solve_times: Vec<f64> = runs.iter().map(|r| r.solve_time.as_secs_f64()).collect();
        
        RunStatistics {
            mean_total_time: Duration::from_secs_f64(Self::mean(&total_times)),
            median_total_time: Duration::from_secs_f64(Self::median(&mut total_times.clone())),
            std_dev_total_time: Duration::from_secs_f64(Self::std_dev(&total_times)),
            mean_solve_time: Duration::from_secs_f64(Self::mean(&solve_times)),
            median_solve_time: Duration::from_secs_f64(Self::median(&mut solve_times.clone())),
            std_dev_solve_time: Duration::from_secs_f64(Self::std_dev(&solve_times)),
            min_total_time: Duration::from_secs_f64(total_times.iter().fold(f64::INFINITY, |a, &b| a.min(b))),
            max_total_time: Duration::from_secs_f64(total_times.iter().fold(0.0, |a, &b| a.max(b))),
            success_rate: runs.iter().map(|r| {
                (r.sat_count + r.unsat_count) as f64 / r.query_count as f64
            }).sum::<f64>() / runs.len() as f64,
        }
    }
    
    /// Generate benchmark suite summary
    fn generate_summary(&self) -> BenchmarkSummary {
        let mut category_stats: HashMap<String, CategoryStatistics> = HashMap::new();
        
        for result in &self.results {
            let category = result.category.clone().unwrap_or_else(|| "default".to_string());
            let stats = category_stats.entry(category).or_insert(CategoryStatistics::default());
            
            stats.benchmark_count += 1;
            stats.total_queries += result.run_results.first().map(|r| r.query_count).unwrap_or(0);
            stats.mean_success_rate += result.statistics.success_rate;
        }
        
        // Normalize success rates
        for stats in category_stats.values_mut() {
            if stats.benchmark_count > 0 {
                stats.mean_success_rate /= stats.benchmark_count as f64;
            }
        }
        
        BenchmarkSummary {
            total_benchmarks: self.results.len(),
            category_statistics: category_stats,
            fastest_benchmark: self.find_fastest_benchmark(),
            slowest_benchmark: self.find_slowest_benchmark(),
            most_successful_benchmark: self.find_most_successful_benchmark(),
        }
    }
    
    /// Find fastest benchmark
    fn find_fastest_benchmark(&self) -> Option<String> {
        self.results.iter()
            .min_by(|a, b| a.statistics.mean_total_time.cmp(&b.statistics.mean_total_time))
            .map(|r| r.benchmark_name.clone())
    }
    
    /// Find slowest benchmark
    fn find_slowest_benchmark(&self) -> Option<String> {
        self.results.iter()
            .max_by(|a, b| a.statistics.mean_total_time.cmp(&b.statistics.mean_total_time))
            .map(|r| r.benchmark_name.clone())
    }
    
    /// Find most successful benchmark
    fn find_most_successful_benchmark(&self) -> Option<String> {
        self.results.iter()
            .max_by(|a, b| a.statistics.success_rate.partial_cmp(&b.statistics.success_rate).unwrap_or(std::cmp::Ordering::Equal))
            .map(|r| r.benchmark_name.clone())
    }
    
    /// Save results to file
    fn save_results(&self, filename: &str, results: &BenchmarkSuiteResult) -> Result<()> {
        let json_data = serde_json::to_string_pretty(results)?;
        let mut file = File::create(filename)?;
        file.write_all(json_data.as_bytes())?;
        info!("Benchmark results saved to {}", filename);
        Ok(())
    }
    
    // Statistical helper functions
    fn mean(values: &[f64]) -> f64 {
        if values.is_empty() { 0.0 } else { values.iter().sum::<f64>() / values.len() as f64 }
    }
    
    fn median(values: &mut [f64]) -> f64 {
        if values.is_empty() { return 0.0; }
        values.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let mid = values.len() / 2;
        if values.len() % 2 == 0 {
            (values[mid - 1] + values[mid]) / 2.0
        } else {
            values[mid]
        }
    }
    
    fn std_dev(values: &[f64]) -> f64 {
        if values.len() < 2 { return 0.0; }
        let mean = Self::mean(values);
        let variance = values.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (values.len() - 1) as f64;
        variance.sqrt()
    }
}

/// Profiler for memory and performance monitoring
pub struct Profiler {
    active_profiles: HashMap<String, ProfileSession>,
}

impl Profiler {
    pub fn new() -> Self {
        Self {
            active_profiles: HashMap::new(),
        }
    }
    
    pub fn start_profiling(&mut self, name: &str) {
        let session = ProfileSession {
            start_time: Instant::now(),
            start_memory: self.get_current_memory_usage(),
            samples: Vec::new(),
        };
        self.active_profiles.insert(name.to_string(), session);
    }
    
    pub fn stop_profiling(&mut self, name: &str) -> Option<ProfileData> {
        if let Some(session) = self.active_profiles.remove(name) {
            let end_time = Instant::now();
            let end_memory = self.get_current_memory_usage();
            
            Some(ProfileData {
                duration: end_time - session.start_time,
                memory_delta: end_memory as i64 - session.start_memory as i64,
                peak_memory: session.samples.iter().max().copied().unwrap_or(session.start_memory),
                sample_count: session.samples.len(),
            })
        } else {
            None
        }
    }
    
    pub fn get_current_memory_usage(&self) -> u64 {
        // Placeholder - in real implementation would use system APIs
        // to get actual memory usage
        0
    }
}

/// Benchmark configuration
#[derive(Debug, Clone)]
pub struct BenchmarkConfig {
    pub runs_per_benchmark: usize,
    pub timeout_per_query_ms: u32,
    pub delay_between_benchmarks: Option<Duration>,
    pub output_file: Option<String>,
    pub enable_profiling: bool,
}

impl Default for BenchmarkConfig {
    fn default() -> Self {
        Self {
            runs_per_benchmark: 3,
            timeout_per_query_ms: 5000,
            delay_between_benchmarks: None,
            output_file: None,
            enable_profiling: true,
        }
    }
}

/// Individual benchmark definition
#[derive(Debug, Clone)]
pub struct Benchmark {
    pub name: String,
    pub category: Option<String>,
    pub description: String,
    pub queries: Vec<BenchmarkQuery>,
    pub timeout_ms: u32,
    pub solver_config: crate::config::Config,
}

/// Benchmark query types
#[derive(Debug, Clone)]
pub struct BenchmarkQuery {
    pub name: String,
    pub query_type: BenchmarkQueryType,
    pub expected_result: Option<QueryResult>,
}

#[derive(Debug, Clone)]
pub enum BenchmarkQueryType {
    Expression(Expr),
    SMTLib(String),
    Custom(Vec<u8>),
}

/// Query execution results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum QueryResult {
    Sat,
    Unsat,
    Unknown,
    Error(String),
}

/// Results from benchmark suite execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkSuiteResult {
    pub total_time: Duration,
    pub benchmark_count: usize,
    pub results: Vec<BenchmarkResult>,
    pub summary: BenchmarkSummary,
}

/// Results from a single benchmark
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkResult {
    pub benchmark_name: String,
    pub category: Option<String>,
    pub run_results: Vec<SingleRunResult>,
    pub statistics: RunStatistics,
}

/// Results from a single benchmark run
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SingleRunResult {
    pub total_time: Duration,
    pub solve_time: Duration,
    pub query_count: usize,
    pub sat_count: usize,
    pub unsat_count: usize,
    pub timeout_count: usize,
    pub query_results: Vec<QueryExecutionResult>,
    pub profile_data: Option<ProfileData>,
    pub solver_statistics: Statistics,
}

/// Results from executing a single query
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueryExecutionResult {
    pub query_index: usize,
    pub result: QueryResult,
    pub execution_time: Duration,
    pub memory_usage: u64,
}

/// Statistical analysis of benchmark runs
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct RunStatistics {
    pub mean_total_time: Duration,
    pub median_total_time: Duration,
    pub std_dev_total_time: Duration,
    pub mean_solve_time: Duration,
    pub median_solve_time: Duration,
    pub std_dev_solve_time: Duration,
    pub min_total_time: Duration,
    pub max_total_time: Duration,
    pub success_rate: f64,
}

/// Profiling data
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfileData {
    pub duration: Duration,
    pub memory_delta: i64,
    pub peak_memory: u64,
    pub sample_count: usize,
}

/// Profile session
#[derive(Debug)]
pub struct ProfileSession {
    pub start_time: Instant,
    pub start_memory: u64,
    pub samples: Vec<u64>,
}

/// Benchmark suite summary
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkSummary {
    pub total_benchmarks: usize,
    pub category_statistics: HashMap<String, CategoryStatistics>,
    pub fastest_benchmark: Option<String>,
    pub slowest_benchmark: Option<String>,
    pub most_successful_benchmark: Option<String>,
}

/// Statistics per benchmark category
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CategoryStatistics {
    pub benchmark_count: usize,
    pub total_queries: usize,
    pub mean_success_rate: f64,
}

/// Benchmark builder for easy benchmark creation
pub struct BenchmarkBuilder {
    benchmark: Benchmark,
}

impl BenchmarkBuilder {
    pub fn new(name: &str) -> Self {
        Self {
            benchmark: Benchmark {
                name: name.to_string(),
                category: None,
                description: String::new(),
                queries: Vec::new(),
                timeout_ms: 5000,
                solver_config: crate::config::Config::default(),
            },
        }
    }
    
    pub fn category(mut self, category: &str) -> Self {
        self.benchmark.category = Some(category.to_string());
        self
    }
    
    pub fn description(mut self, description: &str) -> Self {
        self.benchmark.description = description.to_string();
        self
    }
    
    pub fn timeout(mut self, timeout_ms: u32) -> Self {
        self.benchmark.timeout_ms = timeout_ms;
        self
    }
    
    pub fn add_expression_query(mut self, name: &str, expr: Expr) -> Self {
        self.benchmark.queries.push(BenchmarkQuery {
            name: name.to_string(),
            query_type: BenchmarkQueryType::Expression(expr),
            expected_result: None,
        });
        self
    }
    
    pub fn add_smtlib_query(mut self, name: &str, smtlib: &str) -> Self {
        self.benchmark.queries.push(BenchmarkQuery {
            name: name.to_string(),
            query_type: BenchmarkQueryType::SMTLib(smtlib.to_string()),
            expected_result: None,
        });
        self
    }
    
    pub fn build(self) -> Benchmark {
        self.benchmark
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_benchmark_builder() {
        let benchmark = BenchmarkBuilder::new("test_benchmark")
            .category("arithmetic")
            .description("Test arithmetic operations")
            .timeout(1000)
            .build();
        
        assert_eq!(benchmark.name, "test_benchmark");
        assert_eq!(benchmark.category, Some("arithmetic".to_string()));
        assert_eq!(benchmark.timeout_ms, 1000);
    }
    
    #[test]
    fn test_statistical_functions() {
        let values = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        
        assert_eq!(BenchmarkSuite::mean(&values), 3.0);
        
        let mut values_copy = values.clone();
        assert_eq!(BenchmarkSuite::median(&mut values_copy), 3.0);
        
        let std_dev = BenchmarkSuite::std_dev(&values);
        assert!((std_dev - 1.5811388300841898).abs() < 1e-10);
    }
    
    #[test]
    fn test_benchmark_config() {
        let config = BenchmarkConfig::default();
        
        assert_eq!(config.runs_per_benchmark, 3);
        assert_eq!(config.timeout_per_query_ms, 5000);
        assert!(config.enable_profiling);
    }
}
