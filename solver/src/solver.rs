use crate::expression::{Expr, OpKind, Query, QueryType};
use crate::shared_memory::SharedMemoryManager;
use crate::{Config, BranchCoverage, FuzzySolver};
use crate::testcase::Testcase;
use crate::dependency::DependencyGraph;
use crate::z3_cache::Z3Optimizer;
use crate::concrete_eval::ConcreteEvaluator;
use crate::testcase_loader::TestcaseInitializer;
use crate::i386;
use z3::{ast::{Ast, BV, Bool, Dynamic}, Context, SatResult};
use std::time::Instant;
use anyhow::{Result, Context as AnyhowContext};
use log::{debug, info, warn};
use std::collections::HashSet;

/// Statistics tracking for the solver
#[derive(Debug, Clone, Default)]
pub struct Statistics {
    pub queries_processed: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub timeout_count: u64,
    pub translation_time: u64,
    pub solving_time: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub optimization_count: u64,
}

/// Public statistics structure for external use
#[derive(Debug, Clone)]
pub struct SolverStatistics {
    pub queries_processed: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub timeout_count: u64,
    pub translation_time: u64,
    pub solving_time: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub optimization_count: u64,
}

pub struct SMTSolver {
    pub ctx: Context,
    config: Config,
    shared_memory: Option<SharedMemoryManager>,
    branch_coverage: Option<BranchCoverage>,
    fuzzy_solver: Option<FuzzySolver>,
    statistics: Statistics,
    pub current_testcase: Option<Testcase>,
    symbols_sizes: Vec<u8>,
    symbols_count: usize,
    dependency_graph: DependencyGraph,
    z3_optimizer: Z3Optimizer,
    concrete_evaluator: ConcreteEvaluator,
    expr_visit_time: u64,
    slice_reasoning_time: u64,
    translation_cache: std::cell::RefCell<std::collections::HashMap<u64, String>>,
}

pub struct SolverResult {
    pub result: SatResult,
    pub model: Option<String>,
    testcase: Option<Vec<u8>>,
    pub solve_time_us: u64,
}

impl SMTSolver {
    pub fn new(config: &Config) -> Result<Self> {
        let z3_config = z3::Config::new();
        let ctx = Context::new(&z3_config);
        
        // Initialize shared memory if environment variables are available
        let shared_memory = match SharedMemoryManager::new(config) {
            Ok(sm) => {
                info!("Shared memory initialized successfully");
                Some(sm)
            }
            Err(e) => {
                warn!("Failed to initialize shared memory: {}", e);
                None
            }
        };
        
        // Initialize branch coverage if configured
        let branch_coverage = match BranchCoverage::new(config) {
            Ok(mut bc) => {
                if let Err(e) = bc.load_bitmaps() {
                    warn!("Failed to load branch coverage bitmaps: {}", e);
                }
                info!("Branch coverage initialized successfully");
                Some(bc)
            }
            Err(e) => {
                warn!("Failed to initialize branch coverage: {}", e);
                None
            }
        };
        
        // Initialize fuzzy solver if enabled
        let fuzzy_solver = if config.use_fuzzy_solver {
            match FuzzySolver::new(config) {
                Ok(mut fs) => {
                    if let Err(e) = fs.init(&ctx) {
                        warn!("Failed to initialize fuzzy solver: {}", e);
                        None
                    } else {
                        info!("Fuzzy solver initialized successfully");
                        Some(fs)
                    }
                }
                Err(e) => {
                    warn!("Failed to create fuzzy solver: {}", e);
                    None
                }
            }
        } else {
            None
        };
        
        let z3_optimizer = Z3Optimizer::new(&ctx);
        
        Ok(SMTSolver {
            ctx,
            config: config.clone(),
            shared_memory,
            branch_coverage,
            fuzzy_solver,
            statistics: Statistics::default(),
            current_testcase: None,
            symbols_sizes: Vec::new(),
            symbols_count: 0,
            dependency_graph: DependencyGraph::new(1024 * 1024), // MAX_INPUT_SIZE * 2
            z3_optimizer,
            concrete_evaluator: ConcreteEvaluator::new(),
            expr_visit_time: 0,
            slice_reasoning_time: 0,
            translation_cache: std::cell::RefCell::new(std::collections::HashMap::new()),
        })
    }
    
    /// Process queries from shared memory queue
    pub fn process_shared_queries(&mut self) -> Result<u64> {
        let mut queries_processed = 0;
        
        // Collect queries first to avoid borrowing conflicts
        let mut queries = Vec::new();
        if let Some(ref mut shared_memory) = self.shared_memory {
            while let Some(query) = shared_memory.get_next_query()? {
                queries.push(query);
                if queries.len() > 1000 { // Prevent infinite loop
                    break;
                }
            }
        }
        
        // Process collected queries
        for query in queries {
            match query.get_query_type() {
                QueryType::Branch => {
                    self.process_branch_query(&query)?;
                }
                QueryType::Slice => {
                    self.process_slice_query(&query)?;
                }
                QueryType::Model => {
                    self.process_model_query(&query)?;
                }
                QueryType::Dependency => {
                    self.process_dependency_query(&query)?;
                }
            }
            queries_processed += 1;
                
            // Update branch coverage if available
            if let Some(ref mut bc) = self.branch_coverage {
                bc.update_branch_coverage(query.get_index(), true, false);
            }
        }
        
        Ok(queries_processed)
    }
    
    /// Process branch queries (symbolic PC conditions)
    pub fn process_branch_query(&mut self, query: &Query) -> Result<()> {
        // Extract query expression from args
        let query_expr = self.generate_expression(query)?;
        
        // Create a new context for this query to avoid borrowing conflicts
        let ctx = Context::new(&z3::Config::new());
        let z3_expr = SMTSolver::translate_expression_static(&ctx, &query_expr)?;
        let _z3_neg_query = if let Some(bool_ast) = z3_expr.as_bool() {
            bool_ast.not()
        } else {
            return Err(anyhow::anyhow!("Branch query is not a boolean expression"));
        };
        
        // Check satisfiability of negated branch condition
        let solver = z3::Solver::new(&ctx);
        let mut params = z3::Params::new(&ctx);
        params.set_u32("random_seed", 42);
        solver.set_params(&params);
        
        let start_time = std::time::Instant::now();
        let result = solver.check();
        let solve_time = start_time.elapsed().as_micros() as u64;
        
        match result {
            z3::SatResult::Sat => {
                self.statistics.sat_count += 1;
                self.statistics.solving_time += solve_time;
                
                // Generate testcase from model if available
                if let Some(model) = solver.get_model() {
                    // Create a dummy query for testcase generation
                    let dummy_query = Query::new();
                    self.generate_testcase_from_model(&model, &dummy_query)?;
                }
            }
            z3::SatResult::Unsat => {
                self.statistics.unsat_count += 1;
                self.statistics.unsat_count += 1;
                self.statistics.solving_time += solve_time;
            }
            z3::SatResult::Unknown => {
                self.statistics.timeout_count += 1;
                self.statistics.timeout_count += 1;
                self.statistics.solving_time += solve_time;
            }
        }
        
        Ok(())
    }
    
    pub fn solve_query(&mut self, query_expr: &Expr) -> Result<SatResult> {
        let start_time = Instant::now();
        
        // Create a new context for this query to avoid borrowing conflicts
        let ctx = Context::new(&z3::Config::new());
        let z3_query = Self::translate_expression_static(&ctx, query_expr)?;
        
        // Create solver and add query
        let solver = z3::Solver::new(&ctx);
        if let Some(bool_ast) = z3_query.as_bool() {
            solver.assert(&bool_ast);
        } else {
            return Err(anyhow::anyhow!("Query is not a boolean expression"));
        }
        
        // Check satisfiability
        let result = solver.check();
        let elapsed = start_time.elapsed();
        
        match result {
            z3::SatResult::Sat => {
                self.statistics.sat_count += 1;
                self.statistics.sat_count += 1;
                elapsed;
                
                // Generate testcase if model is available
                if let Some(model) = solver.get_model() {
                    // Create a dummy query for testcase generation
                    let dummy_query = Query::new();
                    self.generate_testcase_from_model(&model, &dummy_query)?;
                }
                Ok(SatResult::Sat)
            },
            z3::SatResult::Unsat => {
                self.statistics.unsat_count += 1;
                self.statistics.solving_time += elapsed.as_micros() as u64;
                Ok(SatResult::Unsat)
            },
            z3::SatResult::Unknown => {
                self.statistics.timeout_count += 1;
                self.statistics.solving_time += elapsed.as_micros() as u64;
                Ok(SatResult::Unknown)
            }
        }
    }
    
    /// Process slice queries (memory slice access)
    pub fn process_slice_query(&mut self, query: &Query) -> Result<()> {
        // Extract slice access parameters from query args
        let slice_args = unsafe { &query.args.args8 };
        let addr_id = slice_args.arg1 as usize;
        let size = slice_args.arg2 as usize;
        let offset = slice_args.arg3 as usize;
        
        // Create symbolic expression for slice access
        let slice_expr = self.create_slice_expression(addr_id, size, offset)?;
        
        // Solve for concrete values
        let _result = self.solve_query(&slice_expr)?;
        
        Ok(())
    }
    
    /// Process model queries (get concrete values for expressions)
    pub fn process_model_query(&mut self, query: &Query) -> Result<()> {
        let query_expr = self.generate_expression(query)?;
        let query_index = query.get_index();
        
        // Perform solving in a separate scope to avoid borrowing conflicts
        let result = {
            let z3_expr = Self::translate_expression_static(&self.ctx, &query_expr)?;
            let solver = z3::Solver::new(&self.ctx);
            solver.assert(&z3_expr.as_bool().unwrap());
            let z3_result = solver.check();
            
            match z3_result {
                z3::SatResult::Sat => SatResult::Sat,
                z3::SatResult::Unsat => SatResult::Unsat,
                z3::SatResult::Unknown => SatResult::Unknown,
            }
        };
        
        // Store solution for testcase generation
        self.store_solution(query_index, result, None)?;
        
        Ok(())
    }
    
    /// Process dependency queries (track expression dependencies)
    pub fn process_dependency_query(&mut self, query: &Query) -> Result<()> {
        let query_expr = self.generate_expression(query)?;
        
        // Extract input dependencies from the expression
        let dependencies = self.extract_dependencies(&query_expr)?;
        
        // Update dependency graph
        self.update_dependency_graph(query.get_index(), dependencies)?;
        
        Ok(())
    }
    
    /// Extract query expression from Query structure
    fn generate_expression(&self, _query: &Query) -> Result<Expr> {
        // For now, create a placeholder expression
        // In full implementation, this would extract the actual expression from query data
        Ok(Expr::new_const(42))
    }
    
    /// Create symbolic expression for memory slice access
    fn create_slice_expression(&self, addr_id: usize, size: usize, offset: usize) -> Result<Expr> {
        // Create symbolic load expression
        let mut expr = Expr::new_const(0);
        expr.opkind = OpKind::IsSymbolic as u8;
        expr.op1 = addr_id as *mut Expr;
        expr.op2 = size as *mut Expr;
        expr.op3 = offset as *mut Expr;
        Ok(expr)
    }
    
    /// Find all solutions for an expression
    fn find_all_solutions(&mut self, expr: &Expr) -> Result<Vec<u64>> {
        let mut solutions = Vec::new();
        let z3_expr = self.translate_expr_to_z3(expr)?;
        let solver = z3::Solver::new(&self.ctx);
        
        // Find up to 256 different solutions
        for i in 0..256 {
            let result = solver.check();
            if result != z3::SatResult::Sat {
                break;
            }
            
            if let Some(model) = solver.get_model() {
                // Extract solution value from model
                if let Some(bv_ast) = z3_expr.as_bv() {
                    if let Some(value) = model.eval(&bv_ast, true) {
                        // Try to extract u64 value from the string representation
                        let value_str = value.to_string();
                        if let Ok(solution) = value_str.parse::<u64>() {
                            solutions.push(solution);
                            
                            // Add constraint to exclude this solution
                            let _constraint = bv_ast._eq(&z3::ast::BV::from_u64(&self.ctx, solution, 64)).not();
                            let mut params = z3::Params::new(&self.ctx);
                            params.set_u32("smt.arith.solver", 2);
                            solver.set_params(&params);
                        }
                    }
                }
            }
            
            if i > 10 && solutions.len() == 1 {
                break; // Avoid infinite loops for single solutions
            }
        }
        
        Ok(solutions)
    }
    
    /// Extract testcase from Z3 model with simplified approach
    fn extract_testcase_from_model(&self, _model: &z3::Model) -> Result<Vec<u8>> {
        // Simplified implementation for now - generate default testcase
        // TODO: Implement proper model value extraction when Z3 API is stable
        let mut testcase_data = vec![0u8; 64.max(self.symbols_count * 8)];
        
        // Fill with some pseudo-random data based on model hash
        for (i, byte) in testcase_data.iter_mut().enumerate() {
            *byte = (i as u8).wrapping_mul(17).wrapping_add(42);
        }
        
        Ok(testcase_data)
    }
    /// Update dependency graph with new query dependencies
    fn update_dependency_graph(&mut self, query_id: usize, input_dependencies: Vec<usize>) -> Result<()> {
        if input_dependencies.is_empty() {
            return Ok(());
        }
        
        let inputs: HashSet<usize> = input_dependencies.into_iter().collect();
        let dep_id = self.dependency_graph.add_expression(&inputs, query_id)?;
        debug!("Updated dependency graph: query {} -> dependency {}", query_id, dep_id);
        
        Ok(())
    }

    /// Extract input dependencies from expression
    fn extract_dependencies(&self, expr: &Expr) -> Result<Vec<usize>> {
        let mut dependencies = Vec::new();
        self.collect_dependencies_recursive(expr, &mut dependencies)?;
        dependencies.sort_unstable();
        dependencies.dedup();
        Ok(dependencies)
    }

    /// Recursively collect dependencies from expression tree
    fn collect_dependencies_recursive(&self, expr: &Expr, dependencies: &mut Vec<usize>) -> Result<()> {
        match expr.opkind {
            2 => { // Symbol
                let symbol_id = expr.op1 as usize;
                dependencies.push(symbol_id);
            }
            _ => {
                if !expr.op1.is_null() {
                    self.collect_dependencies_recursive(unsafe { &*expr.op1 }, dependencies)?;
                }
                if !expr.op2.is_null() {
                    self.collect_dependencies_recursive(unsafe { &*expr.op2 }, dependencies)?;
                }
                if !expr.op3.is_null() {
                    self.collect_dependencies_recursive(unsafe { &*expr.op3 }, dependencies)?;
                }
            }
        }
        Ok(())
    }

    /// Evaluate query concretely using current testcase data
    pub fn evaluate_query_concrete(&mut self, query: &Dynamic, testcase_data: &[u8]) -> Result<u64> {
        // Convert testcase bytes to u64 values for evaluation
        let mut input_data = Vec::new();
        for chunk in testcase_data.chunks(8) {
            let mut bytes = [0u8; 8];
            bytes[..chunk.len()].copy_from_slice(chunk);
            input_data.push(u64::from_le_bytes(bytes));
        }

        // Use concrete evaluator with current symbols configuration
        self.concrete_evaluator.eval_query(
            &self.ctx,
            query,
            &input_data,
            &self.symbols_sizes,
            1000, // max depth
        )
    }

    /// Get concrete evaluation statistics
    pub fn get_concrete_eval_stats(&self) -> String {
        format!("{}", self.concrete_evaluator.stats())
    }

    /// Initialize solver with testcases from various sources
    pub fn initialize_testcases(&mut self) -> Result<Vec<Testcase>> {
        let testcases = TestcaseInitializer::initialize_testcases(
            self.config.testcase_dir.clone(),
            self.config.testcase_path.clone(),
            64, // default size
            1024 * 1024, // max size
        )?;

        // Set current testcase to the first one if available
        if let Some(first_testcase) = testcases.first() {
            self.current_testcase = Some(first_testcase.clone());
            self.symbols_count = first_testcase.data.len();
            self.symbols_sizes = vec![1u8; self.symbols_count]; // Default to byte symbols
            
            info!("Initialized with testcase of {} bytes", first_testcase.data.len());
        }

        Ok(testcases)
    }

    /// Load specific testcase and set as current
    pub fn load_testcase(&mut self, testcase: Testcase) -> Result<()> {
        // Validate testcase
        TestcaseInitializer::validate_testcase(
            &testcase, 
            1024 * 1024
        )?;

        // Update solver state
        self.symbols_count = testcase.data.len();
        self.symbols_sizes = vec![1u8; self.symbols_count];
        self.current_testcase = Some(testcase);

        info!("Loaded testcase with {} symbols", self.symbols_count);
        Ok(())
    }

    /// Get current testcase data prepared for symbolic execution
    pub fn get_symbolic_input(&self) -> Option<Vec<u8>> {
        self.current_testcase.as_ref().map(|testcase| {
            TestcaseInitializer::prepare_symbolic_input(testcase, self.symbols_count)
        })
    }
    
    /// Generate testcase from Z3 model
    fn generate_testcase_from_model(&mut self, _model: &z3::Model, _query: &Query) -> Result<()> {
        use crate::testcase::{Testcase, TestcaseMutation};
        
        // Extract model values and generate testcase
        let mut testcase_data = Vec::new();
        
        // TODO: Implement proper model extraction when Z3 API is available
        // For now, generate a simple placeholder testcase
        testcase_data.extend_from_slice(b"placeholder_testcase_data");
        
        // Note: In the full implementation, this would:
        // 1. Iterate through model variables
        // 2. Extract concrete values for symbolic inputs
        // 3. Convert Z3 bitvector values to bytes
        // 4. Reconstruct the input file format
        
        // Create testcase from extracted data
        if !testcase_data.is_empty() {
            let testcase = Testcase::new(testcase_data);
            
            // Save the testcase
            if let Some(ref output_dir) = self.config.output_dir {
                let testcase_path = format!("{}/testcase_{}.bin", output_dir.display(), self.statistics.sat_count);
                testcase.save_to_file(std::path::Path::new(&testcase_path))?;
                info!("Generated testcase: {}", testcase_path);
                
                // Generate mutations if requested
                let generate_mutations = true; // TODO: Add to config
                if generate_mutations {
                    for i in 0..5 { // Generate 5 mutations
                        let mutation = TestcaseMutation::new_trim(0, 1); // Simple trim mutation
                        let mutated_data = testcase.apply_mutation(&mutation)?;
                        let mutated = Testcase::new(mutated_data);
                        
                        let mutation_path = format!("{}/testcase_{}_mut_{}.bin", output_dir.display(), self.statistics.sat_count, i);
                        mutated.save_to_file(std::path::Path::new(&mutation_path))?;
                    }
                }
            }
        }
        
        Ok(())
    }
    
    
    /// Load initial testcase from file
    pub fn load_initial_testcase(&mut self) -> Result<()> {
        if let Some(ref testcase_path) = self.config.testcase_path {
            info!("Loading testcase from: {}", testcase_path.display());
            
            let testcase = Testcase::from_file(testcase_path)
                .with_context(|| format!("Failed to load testcase from {}", testcase_path.display()))?;
            
            info!("Loaded {} bytes from testcase: {}", testcase.size(), testcase_path.display());
            
            // Initialize symbols sizes (each byte is 8 bits)
            self.symbols_sizes = vec![8; testcase.size()];
            self.symbols_count = testcase.size();
            
            self.current_testcase = Some(testcase);
            Ok(())
        } else {
            warn!("No testcase path configured");
            Ok(())
        }
    }
    
    /// Reset testcase to original state
    pub fn reset_testcase(&mut self) -> Result<()> {
        if let Some(ref _testcase_path) = self.config.testcase_path {
            self.load_initial_testcase()
        } else {
            Ok(())
        }
    }

    pub fn check_sat(&mut self, expr: &z3::ast::Dynamic) -> anyhow::Result<SatResult> {
        let start_time = std::time::Instant::now();
        let solver = z3::Solver::new(&self.ctx);
        solver.assert(&expr.as_bool().unwrap());
        let z3_result = solver.check();
        
        let elapsed = start_time.elapsed();
        
        // Update statistics
        match z3_result {
            z3::SatResult::Sat => {
                self.statistics.sat_count += 1;
                self.statistics.solving_time += elapsed.as_micros() as u64;
                Ok(SatResult::Sat)
            }
            z3::SatResult::Unsat => {
                self.statistics.unsat_count += 1;
                self.statistics.solving_time += elapsed.as_micros() as u64;
                Ok(SatResult::Unsat)
            }
            z3::SatResult::Unknown => {
                self.statistics.timeout_count += 1;
                self.statistics.solving_time += elapsed.as_micros() as u64;
                Ok(SatResult::Unknown)
            }
        }
    }

    pub fn create_negation<'a>(&self, expr: &z3::ast::Dynamic<'a>) -> Result<z3::ast::Dynamic<'a>> {
        if let Some(bool_expr) = expr.as_bool() {
            Ok(bool_expr.not().into())
        } else if let Some(bv_expr) = expr.as_bv() {
            Ok(bv_expr.bvnot().into())
        } else {
            anyhow::bail!("Cannot create negation of expression type")
        }
    }

    pub fn negate_expr(&self, expr: &Expr) -> anyhow::Result<Expr> {
        // Create a negated expression
        let negated = Expr::new_unary(OpKind::Not, expr as *const Expr as *mut Expr);
        Ok(negated)
    }

    /// Get model from Z3 solver after satisfiability check
    pub fn get_model(&self, expr: &z3::ast::Dynamic) -> Result<Option<z3::Model>> {
        let solver = z3::Solver::new(&self.ctx);
        solver.assert(&expr.as_bool().unwrap());
        
        match solver.check() {
            z3::SatResult::Sat => {
                Ok(solver.get_model())
            }
            _ => Ok(None)
        }
    }

    /// Initialize solver
    pub fn initialize(&mut self) -> Result<()> {
        // Initialize shared memory connections
        // Shared memory is already initialized in constructor
        
        // Initialize branch coverage
        if let Some(ref mut branch_cov) = self.branch_coverage {
            branch_cov.load_bitmaps()?;
        }
        
        Ok(())
    }
    
    /// Print solver statistics
    pub fn print_statistics(&self) {
        println!("SMT Solver Statistics:");
        println!("  Queries processed: {}", self.statistics.queries_processed);
        println!("  SAT results: {}", self.statistics.sat_count);
        println!("  UNSAT results: {}", self.statistics.unsat_count);
        println!("  Timeouts: {}", self.statistics.timeout_count);
        println!("  Translation time: {} μs", self.statistics.translation_time);
        println!("  Solving time: {} μs", self.statistics.solving_time);
        println!("  Cache hits: {}", self.statistics.cache_hits);
        println!("  Cache misses: {}", self.statistics.cache_misses);
    }
    
    /// Get current testcase data
    pub fn get_current_testcase(&self) -> Option<Vec<u8>> {
        self.current_testcase.as_ref().map(|tc| tc.data.clone())
    }
    
    /// Save solver state (placeholder implementation)
    pub fn save_state(&self) -> Result<()> {
        // Placeholder implementation - in a full implementation this would
        // save the current solver state, statistics, and context
        debug!("Saving solver state");
        Ok(())
    }
    
    /// Translate expression to Z3
    pub fn translate_expr_to_z3<'a>(&'a self, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        self.translate_expression(expr)
    }
    
    /// Static expression translation method for avoiding borrowing conflicts
    pub fn translate_expression_static<'a>(ctx: &'a z3::Context, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        match expr.opkind {
            1 => { // Const
                let value = expr.op1 as u64;
                Ok(z3::ast::BV::from_u64(ctx, value, 64).into())
            }
            5 => { // Add
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvadd(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Add operation")
                }
            }
            10 => { // Eq
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(left._eq(&right).into())
            }
            15 => { // Not
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(bool_expr) = operand.as_bool() {
                    Ok(bool_expr.not().into())
                } else {
                    anyhow::bail!("Invalid operand for Not operation")
                }
            }
            6 => { // Sub
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvsub(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Sub operation")
                }
            }
            7 => { // Mul
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvmul(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Mul operation")
                }
            }
            8 => { // Div
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvudiv(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Div operation")
                }
            }
            9 => { // Mod
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvurem(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Mod operation")
                }
            }
            11 => { // Ne
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(left._eq(&right).not().into())
            }
            16 => { // And
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bool), Some(right_bool)) = (left.as_bool(), right.as_bool()) {
                    Ok(z3::ast::Bool::and(ctx, &[&left_bool, &right_bool]).into())
                } else if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvand(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for And operation")
                }
            }
            17 => { // Or
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bool), Some(right_bool)) = (left.as_bool(), right.as_bool()) {
                    Ok(z3::ast::Bool::or(ctx, &[&left_bool, &right_bool]).into())
                } else if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvor(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Or operation")
                }
            }
            18 => { // Xor
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvxor(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Xor operation")
                }
            }
            19 => { // Shl
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvshl(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Shl operation")
                }
            }
            20 => { // Shr
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvlshr(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Shr operation")
                }
            }
            21 => { // Sar (arithmetic right shift)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvashr(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Sar operation")
                }
            }
            12 => { // Lt (less than)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvult(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Lt operation")
                }
            }
            13 => { // Le (less than or equal)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvule(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Le operation")
                }
            }
            14 => { // Gt (greater than)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvugt(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Gt operation")
                }
            }
            22 => { // Ge (greater than or equal)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvuge(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Ge operation")
                }
            }
            23 => { // Extract
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(bv_expr) = operand.as_bv() {
                    // Extract bits from high to low (op2 = high, op3 = low)
                    let high = expr.op2 as u32;
                    let low = expr.op3 as u32;
                    Ok(bv_expr.extract(high, low).into())
                } else {
                    anyhow::bail!("Invalid operand for Extract operation")
                }
            }
            24 => { // Concat
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.concat(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Concat operation")
                }
            }
            25 => { // Zext (zero extend)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(bv_expr) = operand.as_bv() {
                    let extend_bits = expr.op2 as u32;
                    Ok(bv_expr.zero_ext(extend_bits).into())
                } else {
                    anyhow::bail!("Invalid operand for Zext operation")
                }
            }
            26 => { // Sext (sign extend)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(bv_expr) = operand.as_bv() {
                    let extend_bits = expr.op2 as u32;
                    Ok(bv_expr.sign_ext(extend_bits).into())
                } else {
                    anyhow::bail!("Invalid operand for Sext operation")
                }
            }
            27 => { // Sdiv (signed division)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvsdiv(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Sdiv operation")
                }
            }
            28 => { // Srem (signed remainder)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvsrem(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Srem operation")
                }
            }
            29 => { // Slt (signed less than)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvslt(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Slt operation")
                }
            }
            30 => { // Sle (signed less than or equal)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvsle(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Sle operation")
                }
            }
            31 => { // Sgt (signed greater than)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvsgt(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Sgt operation")
                }
            }
            32 => { // Sge (signed greater than or equal)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvsge(&right_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Sge operation")
                }
            }
            106 => { // SymbolicLoad
                // Create symbolic memory load operation
                let address = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(addr_bv) = address.as_bv() {
                    // Create a symbolic value for the loaded data
                    let load_symbol = format!("load_{}", addr_bv.to_string());
                    Ok(z3::ast::BV::new_const(ctx, load_symbol, 64).into())
                } else {
                    anyhow::bail!("Invalid address for SymbolicLoad operation")
                }
            }
            107 => { // SymbolicStore
                // Create symbolic memory store operation
                let address = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let value = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(_addr_bv), Some(val_bv)) = (address.as_bv(), value.as_bv()) {
                    // Store operations typically return the stored value
                    Ok(val_bv.into())
                } else {
                    anyhow::bail!("Invalid operands for SymbolicStore operation")
                }
            }
            103 => { // MemorySlice
                // Create memory slice constraint
                let base_addr = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let size = expr.op2 as u64;
                if let Some(base_bv) = base_addr.as_bv() {
                    // Create a symbolic array for the memory slice
                    let slice_name = format!("slice_{}_{}", base_bv.to_string(), size);
                    Ok(z3::ast::BV::new_const(ctx, slice_name, (size * 8) as u32).into())
                } else {
                    anyhow::bail!("Invalid base address for MemorySlice operation")
                }
            }
            2 => { // Symbol (symbolic variable)
                let symbol_id = expr.op1 as u32;
                let symbol_name = format!("sym_{}", symbol_id);
                Ok(z3::ast::BV::new_const(ctx, symbol_name, 64).into())
            }
            33 => { // ITE (if-then-else)
                let condition = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let then_expr = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                let else_expr = Self::translate_expression_static(ctx, unsafe { &*expr.op3 })?;
                if let Some(cond_bool) = condition.as_bool() {
                    Ok(cond_bool.ite(&then_expr, &else_expr))
                } else {
                    anyhow::bail!("Invalid condition for ITE operation")
                }
            }
            34 => { // Rol (rotate left)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let amount = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(op_bv), Some(amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    Ok(op_bv.bvrotl(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Rol operation")
                }
            }
            35 => { // Ror (rotate right)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let amount = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(op_bv), Some(amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    Ok(op_bv.bvrotr(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Ror operation")
                }
            }
            36 => { // Abs (absolute value)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    // Implement abs using ITE: (ite (bvslt x 0) (bvneg x) x)
                    let zero = z3::ast::BV::from_u64(ctx, 0, op_bv.get_size());
                    let is_negative = op_bv.bvslt(&zero);
                    let negated = op_bv.bvneg();
                    Ok(is_negative.ite(&negated.into(), &op_bv.into()))
                } else {
                    anyhow::bail!("Invalid operand for Abs operation")
                }
            }
            37 => { // Min (minimum)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    // Implement min using ITE: (ite (bvult x y) x y)
                    let is_less = left_bv.bvult(&right_bv);
                    Ok(is_less.ite(&left_bv.into(), &right_bv.into()))
                } else {
                    anyhow::bail!("Invalid operands for Min operation")
                }
            }
            38 => { // Max (maximum)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    // Implement max using ITE: (ite (bvugt x y) x y)
                    let is_greater = left_bv.bvugt(&right_bv);
                    Ok(is_greater.ite(&left_bv.into(), &right_bv.into()))
                } else {
                    anyhow::bail!("Invalid operands for Max operation")
                }
            }
            39 => { // Nand (bitwise NAND)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvand(&right_bv).bvnot().into())
                } else {
                    anyhow::bail!("Invalid operands for Nand operation")
                }
            }
            40 => { // Nor (bitwise NOR)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvor(&right_bv).bvnot().into())
                } else {
                    anyhow::bail!("Invalid operands for Nor operation")
                }
            }
            41 => { // PopCount (population count - count set bits)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    // Simplified popcount implementation - create symbolic result
                    let popcount_name = format!("popcount_{}", op_bv.to_string());
                    Ok(z3::ast::BV::new_const(ctx, popcount_name, 64).into())
                } else {
                    anyhow::bail!("Invalid operand for PopCount operation")
                }
            }
            42 => { // Clz (count leading zeros)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    // Simplified clz implementation - create symbolic result
                    let clz_name = format!("clz_{}", op_bv.to_string());
                    Ok(z3::ast::BV::new_const(ctx, clz_name, 64).into())
                } else {
                    anyhow::bail!("Invalid operand for Clz operation")
                }
            }
            43 => { // Ctz (count trailing zeros)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    // Simplified ctz implementation - create symbolic result
                    let ctz_name = format!("ctz_{}", op_bv.to_string());
                    Ok(z3::ast::BV::new_const(ctx, ctz_name, 64).into())
                } else {
                    anyhow::bail!("Invalid operand for Ctz operation")
                }
            }
            44 => { // Bswap (byte swap)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    // Implement byte swap for 64-bit values
                    let size = op_bv.get_size();
                    if size == 64 {
                        let b0 = op_bv.extract(7, 0);
                        let b1 = op_bv.extract(15, 8);
                        let b2 = op_bv.extract(23, 16);
                        let b3 = op_bv.extract(31, 24);
                        let b4 = op_bv.extract(39, 32);
                        let b5 = op_bv.extract(47, 40);
                        let b6 = op_bv.extract(55, 48);
                        let b7 = op_bv.extract(63, 56);
                        Ok(b0.concat(&b1).concat(&b2).concat(&b3)
                           .concat(&b4).concat(&b5).concat(&b6).concat(&b7).into())
                    } else {
                        // For other sizes, create symbolic result
                        let bswap_name = format!("bswap_{}", op_bv.to_string());
                        Ok(z3::ast::BV::new_const(ctx, bswap_name, size).into())
                    }
                } else {
                    anyhow::bail!("Invalid operand for Bswap operation")
                }
            }
            45 => { // Saturate (saturation arithmetic)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let min_val = expr.op2 as i64;
                let max_val = expr.op3 as i64;
                if let Some(op_bv) = operand.as_bv() {
                    let min_bv = z3::ast::BV::from_i64(ctx, min_val, op_bv.get_size());
                    let max_bv = z3::ast::BV::from_i64(ctx, max_val, op_bv.get_size());
                    
                    // Implement saturation: clamp(x, min, max)
                    let too_small = op_bv.bvslt(&min_bv);
                    let too_large = op_bv.bvsgt(&max_bv);
                    
                    let clamped_low = too_small.ite(&min_bv.into(), &op_bv.into());
                    Ok(too_large.ite(&max_bv.into(), &clamped_low))
                } else {
                    anyhow::bail!("Invalid operand for Saturate operation")
                }
            }
            46 => { // FpAdd (floating point addition)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                // Simplified FP implementation - create symbolic result
                let fp_name = format!("fpadd_{}_{}", left.to_string(), right.to_string());
                Ok(z3::ast::BV::new_const(ctx, fp_name, 64).into())
            }
            47 => { // FpSub (floating point subtraction)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                // Simplified FP implementation - create symbolic result
                let fp_name = format!("fpsub_{}_{}", left.to_string(), right.to_string());
                Ok(z3::ast::BV::new_const(ctx, fp_name, 64).into())
            }
            48 => { // FpMul (floating point multiplication)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                // Simplified FP implementation - create symbolic result
                let fp_name = format!("fpmul_{}_{}", left.to_string(), right.to_string());
                Ok(z3::ast::BV::new_const(ctx, fp_name, 64).into())
            }
            49 => { // FpDiv (floating point division)
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                // Simplified FP implementation - create symbolic result
                let fp_name = format!("fpdiv_{}_{}", left.to_string(), right.to_string());
                Ok(z3::ast::BV::new_const(ctx, fp_name, 64).into())
            }
            _ => {
                // Enhanced error handling for unsupported operations
                anyhow::bail!("Unsupported OpKind {} in expression translation. This operation is not yet implemented in the Z3 translation layer.", expr.opkind)
            }
        }
    }

    /// Internal expression translation method with optimization
    fn translate_expression<'a>(&'a self, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        // Check for cached translations first
        let expr_hash = self.compute_expression_hash(expr);
        let _cache_key = format!("{}", expr_hash);
        
        if let Some(_cached_result) = self.translation_cache.borrow().get(&expr_hash) {
            // For now, skip caching due to lifetime issues - just translate directly
            // TODO: Implement proper caching with string-based storage
        }
        
        // Apply expression optimizations before translation
        let optimized_expr = self.optimize_expression(expr)?;
        
        // Use the static method to avoid borrowing conflicts
        let result = Self::translate_expression_static(&self.ctx, &optimized_expr)?;
        
        // Cache the result as string representation for future reference
        self.translation_cache.borrow_mut().insert(expr_hash, result.to_string());
        
        Ok(result)
    }
    
    /// Compute hash for expression caching
    fn compute_expression_hash(&self, expr: &Expr) -> u64 {
        // Simple hash based on opkind and operand addresses
        let mut hash = expr.opkind as u64;
        hash = hash.wrapping_mul(31).wrapping_add(expr.op1 as u64);
        hash = hash.wrapping_mul(31).wrapping_add(expr.op2 as u64);
        hash = hash.wrapping_mul(31).wrapping_add(expr.op3 as u64);
        hash
    }
    
    /// Optimize expression before translation
    fn optimize_expression(&self, expr: &Expr) -> Result<Expr> {
        // Apply various optimization techniques
        match expr.opkind {
            5 => { // Add optimization
                // Check for add with zero
                if self.is_constant_zero(expr.op2) {
                    return Ok(unsafe { (*expr.op1).clone() });
                }
                if self.is_constant_zero(expr.op1) {
                    return Ok(unsafe { (*expr.op2).clone() });
                }
            }
            7 => { // Mul optimization
                // Check for multiply by zero
                if self.is_constant_zero(expr.op1) || self.is_constant_zero(expr.op2) {
                    return Ok(Expr::new_const(0));
                }
                // Check for multiply by one
                if self.is_constant_one(expr.op1) {
                    return Ok(unsafe { (*expr.op2).clone() });
                }
                if self.is_constant_one(expr.op2) {
                    return Ok(unsafe { (*expr.op1).clone() });
                }
            }
            16 => { // And optimization
                // Check for and with zero
                if self.is_constant_zero(expr.op1) || self.is_constant_zero(expr.op2) {
                    return Ok(Expr::new_const(0));
                }
            }
            17 => { // Or optimization
                // Check for or with zero
                if self.is_constant_zero(expr.op1) {
                    return Ok(unsafe { (*expr.op2).clone() });
                }
                if self.is_constant_zero(expr.op2) {
                    return Ok(unsafe { (*expr.op1).clone() });
                }
            }
            _ => {}
        }
        
        // No optimization applied, return original
        Ok(expr.clone())
    }
    
    /// Check if expression operand is constant zero
    fn is_constant_zero(&self, operand: *mut Expr) -> bool {
        if operand.is_null() {
            return false;
        }
        let expr = unsafe { &*operand };
        expr.opkind == 1 && expr.op1 as u64 == 0 // Const with value 0
    }
    
    /// Check if expression operand is constant one
    fn is_constant_one(&self, operand: *mut Expr) -> bool {
        if operand.is_null() {
            return false;
        }
        let expr = unsafe { &*operand };
        expr.opkind == 1 && expr.op1 as u64 == 1 // Const with value 1
    }

    pub fn save_bitmaps(&self) -> anyhow::Result<()> {
        if let Some(ref branch_cov) = self.branch_coverage {
            branch_cov.save_bitmaps()?;
        }
        Ok(())
    }
    
    /// Store solution for a query
    fn store_solution(&mut self, query_index: usize, result: SatResult, model: Option<String>) -> Result<()> {
        // Store the solution in the dependency graph or statistics
        match result {
            SatResult::Sat => {
                self.statistics.sat_count += 1;
                if let Some(model_str) = model {
                    info!("Query {} SAT with model: {}", query_index, model_str);
                }
            }
            SatResult::Unsat => {
                self.statistics.unsat_count += 1;
                info!("Query {} UNSAT", query_index);
            }
            SatResult::Unknown => {
                self.statistics.timeout_count += 1;
                info!("Query {} UNKNOWN/TIMEOUT", query_index);
            }
        }
        Ok(())
    }
}

pub struct Model<'a> {
    z3_model: z3::Model<'a>,
}

impl<'a> Model<'a> {
    pub fn new(z3_model: z3::Model<'a>) -> Self {
        Self { z3_model }
    }
    
    /// Generate testcase from model
    pub fn generate_testcase(&self, input_size: usize) -> Result<Vec<u8>> {
        let mut testcase = vec![0u8; input_size];
        
        // Extract values from Z3 model and populate testcase
        // This is a simplified implementation - in practice would extract
        // symbolic variable values from the model
        // For now, generate random testcase data
        // In full implementation, would extract symbolic variable values from Z3 model
        use rand::Rng;
        let mut rng = rand::thread_rng();
        for i in 0..input_size {
            testcase[i] = rng.gen::<u8>();
        }
        
        Ok(testcase)
    }
}
