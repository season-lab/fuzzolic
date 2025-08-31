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
        let z3_neg_query = if let Some(bool_ast) = z3_expr.as_bool() {
            bool_ast.not()
        } else {
            return Err(anyhow::anyhow!("Branch query is not a boolean expression"));
        };
        
        // Check satisfiability of negated branch condition
        let solver = z3::Solver::new(&ctx);
        solver.assert(&z3_neg_query);
        
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
        
        // Find all possible solutions for the expression
        let solutions = self.find_all_solutions(&query_expr)?;
        
        // Store solutions for testcase generation
        for solution in solutions {
            self.store_solution(query.get_index(), solution)?;
        }
        
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
                            let constraint = bv_ast._eq(&z3::ast::BV::from_u64(&self.ctx, solution, 64)).not();
                            solver.assert(&constraint);
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
    
    /// Extract input dependencies from expression
    fn extract_dependencies(&self, _expr: &Expr) -> Result<Vec<usize>> {
        // Placeholder implementation
        // In full implementation, this would traverse the expression tree
        // and collect all symbolic input references
        Ok(vec![])
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
    
    /// Store solution for testcase generation
    fn store_solution(&mut self, _query_id: usize, _solution: u64) -> Result<()> {
        // Placeholder implementation
        // In full implementation, this would store the solution for later testcase generation
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
            _ => {
                // Default case for unsupported operations
                Ok(z3::ast::BV::from_u64(ctx, 0, 64).into())
            }
        }
    }

    /// Internal expression translation method
    fn translate_expression<'a>(&'a self, expr: &Expr) -> Result<z3::ast::Dynamic<'a>> {
        match expr.opkind {
            1 => { // Const
                // Extract constant value from expr
                let value = expr.op1 as u64;
                Ok(z3::ast::BV::from_u64(&self.ctx, value, 64).into())
            }
            5 => { // Add
                let left = self.translate_expression(unsafe { &*expr.op1 })?;
                let right = self.translate_expression(unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvadd(&rbv).into())
                } else {
                    anyhow::bail!("Type mismatch in Add operation")
                }
            }
            6 => { // Sub
                let left = self.translate_expression(unsafe { &*expr.op1 })?;
                let right = self.translate_expression(unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvsub(&rbv).into())
                } else {
                    anyhow::bail!("Type mismatch in Sub operation")
                }
            }
            22 => { // Eq
                let left = self.translate_expression(unsafe { &*expr.op1 })?;
                let right = self.translate_expression(unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv._eq(&rbv).into())
                } else {
                    anyhow::bail!("Type mismatch in Eq operation")
                }
            }
            4 => { // Not
                let operand = self.translate_expression(unsafe { &*expr.op1 })?;
                if let Some(bool_expr) = operand.as_bool() {
                    Ok(bool_expr.not().into())
                } else if let Some(bv_expr) = operand.as_bv() {
                    Ok(bv_expr.bvnot().into())
                } else {
                    anyhow::bail!("Type mismatch in Not operation")
                }
            }
            _ => {
                // For now, return a placeholder constant for unsupported operations
                warn!("Unsupported operation: {}", expr.opkind);
                Ok(z3::ast::BV::from_u64(&self.ctx, 0, 64).into())
            }
        }
    }

    pub fn save_bitmaps(&self) -> anyhow::Result<()> {
        if let Some(ref branch_cov) = self.branch_coverage {
            branch_cov.save_bitmaps()?;
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
    
    // Remove this method as it's incorrectly placed in Model struct
}
