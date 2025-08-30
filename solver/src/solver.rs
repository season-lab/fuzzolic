use crate::expression::{Expr, OpKind, Query, QueryType};
use crate::shared_memory::SharedMemoryManager;
use crate::{Config, BranchCoverage, FuzzySolver};
use crate::testcase::Testcase;
use crate::i386;
use z3::{ast::{Ast, BV, Bool, Dynamic}, Context, SatResult};
use anyhow::{Result, Context as AnyhowContext};
use log::{info, warn};
use std::time::Instant;

pub struct SMTSolver {
    ctx: Context,
    config: Config,
    shared_memory: Option<SharedMemoryManager>,
    branch_coverage: Option<BranchCoverage>,
    fuzzy_solver: Option<FuzzySolver>,
    sat_count: u64,
    sat_time: u64,
    unsat_count: u64,
    unsat_time: u64,
    timeout_count: u64,
    unknown_count: u64,
    unknown_time: u64,
    current_testcase: Option<Testcase>,
    symbols_sizes: Vec<u8>,
    symbols_count: usize,
    translation_time: u64,
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
        
        Ok(SMTSolver {
            ctx,
            config: config.clone(),
            shared_memory,
            branch_coverage,
            fuzzy_solver,
            sat_count: 0,
            sat_time: 0,
            unsat_count: 0,
            unsat_time: 0,
            timeout_count: 0,
            unknown_count: 0,
            unknown_time: 0,
            current_testcase: None,
            symbols_sizes: Vec::new(),
            symbols_count: 0,
            translation_time: 0,
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
        let query_expr = self.extract_query_expression(query)?;
        
        // Create a new context for this query to avoid borrowing conflicts
        let ctx = Context::new(&z3::Config::new());
        let z3_query = self.translate_expr_to_z3_with_ctx(&ctx, &query_expr)?;
        let z3_neg_query = if let Some(bool_ast) = z3_query.as_bool() {
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
                self.sat_count += 1;
                self.sat_time += solve_time;
                
                // Generate testcase from model if available
                if let Some(model) = solver.get_model() {
                    // Create a dummy query for testcase generation
                    let dummy_query = Query::new();
                    self.generate_testcase_from_model(&model, &dummy_query)?;
                }
            }
            z3::SatResult::Unsat => {
                self.unsat_count += 1;
                self.unsat_time += solve_time;
            }
            z3::SatResult::Unknown => {
                self.unknown_count += 1;
                self.unknown_time += solve_time;
            }
        }
        
        Ok(())
    }
    
    pub fn solve_query(&mut self, query_expr: &Expr) -> Result<SatResult> {
        let start_time = Instant::now();
        
        // Create a new context for this query to avoid borrowing conflicts
        let ctx = Context::new(&z3::Config::new());
        let z3_query = self.translate_expr_to_z3_with_ctx(&ctx, query_expr)?;
        
        // Create solver and add query
        let solver = z3::Solver::new(&ctx);
        if let Some(bool_ast) = z3_query.as_bool() {
            solver.assert(&bool_ast);
        } else {
            return Err(anyhow::anyhow!("Query is not a boolean expression"));
        }
        
        // Check satisfiability
        let result = solver.check();
        let elapsed = start_time.elapsed().as_millis() as u64;
        
        match result {
            z3::SatResult::Sat => {
                self.sat_count += 1;
                self.sat_time += elapsed;
                
                // Generate testcase if model is available
                if let Some(model) = solver.get_model() {
                    // Create a dummy query for testcase generation
                    let dummy_query = Query::new();
                    self.generate_testcase_from_model(&model, &dummy_query)?;
                }
                Ok(SatResult::Sat)
            },
            z3::SatResult::Unsat => {
                self.unsat_count += 1;
                self.unsat_time += elapsed;
                Ok(SatResult::Unsat)
            },
            z3::SatResult::Unknown => {
                self.unknown_count += 1;
                self.unknown_time += elapsed;
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
        let query_expr = self.extract_query_expression(query)?;
        
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
        let query_expr = self.extract_query_expression(query)?;
        
        // Extract input dependencies from the expression
        let dependencies = self.extract_dependencies(&query_expr)?;
        
        // Update dependency graph
        self.update_dependency_graph(query.get_index(), dependencies)?;
        
        Ok(())
    }
    
    /// Extract query expression from Query structure
    fn extract_query_expression(&self, query: &Query) -> Result<Expr> {
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
        
        let z3_query = self.translate_expr_to_z3(expr)?;
        let solver = z3::Solver::new(&self.ctx);
        
        // Find up to 256 different solutions
        for i in 0..256 {
            let result = solver.check();
            if result != z3::SatResult::Sat {
                break;
            }
            
            if let Some(model) = solver.get_model() {
                // Extract solution value from model
                if let Some(bv_ast) = z3_query.as_bv() {
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
    
    /// Update dependency graph with new dependencies
    fn update_dependency_graph(&mut self, _query_id: usize, _dependencies: Vec<usize>) -> Result<()> {
        // Placeholder implementation
        // In full implementation, this would update the dependency tracking structures
        Ok(())
    }
    
    /// Generate testcase from Z3 model
    fn generate_testcase_from_model(&mut self, model: &z3::Model, _query: &Query) -> Result<()> {
        use crate::testcase::{Testcase, TestcaseMutation};
        
        // Extract model values and generate testcase
        let mut testcase_data = Vec::new();
        
        // For now, create a simple testcase based on model
        // In full implementation, this would extract actual variable assignments
        for i in 0..256 {
            let var_name = format!("input_{}", i);
            
            // Try to get value from model (simplified approach)
            // In real implementation, we'd have proper symbol mapping
            testcase_data.push((i % 256) as u8);
        }
        
        // Create testcase with mutations
        let mut testcase = Testcase::new(testcase_data);
        
        // Add some basic mutations for fuzzing
        testcase.add_mutation(TestcaseMutation::new_trim(10, 5));
        testcase.add_mutation(TestcaseMutation::new_replace(20, vec![0xFF, 0xFE, 0xFD]));
        testcase.add_mutation(TestcaseMutation::new_extend(50, vec![0x41, 0x42, 0x43]));
        
        // Save testcase to output directory if configured
        if let Some(ref output_dir) = self.config.output_dir {
            let output_path = std::path::Path::new(output_dir);
            if let Err(e) = std::fs::create_dir_all(output_path) {
                warn!("Failed to create output directory: {}", e);
                return Ok(());
            }
            
            match testcase.save_to_file(output_path) {
                Ok(saved_files) => {
                    info!("Generated {} testcase files", saved_files.len());
                    for file in saved_files {
                        info!("Saved testcase: {}", file.display());
                    }
                }
                Err(e) => {
                    warn!("Failed to save testcase: {}", e);
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
            info!("Loading testcase: {}", testcase_path.display());
            
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
        if let Some(ref testcase_path) = self.config.testcase_path {
            self.load_initial_testcase()
        } else {
            Ok(())
        }
    }
    
    /// Get current testcase data
    pub fn get_testcase_data(&self) -> Option<&[u8]> {
        self.current_testcase.as_ref().map(|tc| tc.data.as_slice())
    }
    
    /// Mutate testcase at specific byte offset
    pub fn mutate_testcase_byte(&mut self, offset: usize, value: u8) -> Result<()> {
        if let Some(ref mut testcase) = self.current_testcase {
            if offset < testcase.data.len() {
                testcase.data[offset] = value;
                Ok(())
            } else {
                anyhow::bail!("Testcase mutation offset {} out of bounds (size: {})", offset, testcase.data.len())
            }
        } else {
            anyhow::bail!("No testcase loaded for mutation")
        }
    }
    
    /// Apply mutations to create new testcase variants
    pub fn generate_mutated_testcases(&mut self, mutations: Vec<crate::testcase::TestcaseMutation>) -> Result<Vec<Testcase>> {
        if let Some(ref testcase) = self.current_testcase {
            let mut variants = Vec::new();
            
            for mutation in mutations {
                let mut variant = testcase.clone();
                variant.add_mutation(mutation);
                variants.push(variant);
            }
            
            Ok(variants)
        } else {
            anyhow::bail!("No testcase loaded for mutation generation")
        }
    }
    
    /// Save solver state (bitmaps, statistics, etc.)
    pub fn save_state(&mut self) -> Result<()> {
        // Save branch coverage bitmap if available
        if let Some(ref branch_coverage) = self.branch_coverage {
            if let Err(e) = branch_coverage.save_bitmaps() {
                warn!("Failed to save branch coverage bitmaps: {}", e);
            }
        }
        
        // Save any other persistent state here
        info!("Solver state saved successfully");
        Ok(())
    }
    
    
    pub fn translate_expr_to_z3_with_ctx<'ctx>(&self, ctx: &'ctx Context, expr: &Expr) -> anyhow::Result<Dynamic<'ctx>> {
        match OpKind::try_from(expr.opkind)? {
            OpKind::IsConst => {
                // Extract constant value from pointer cast
                let value = expr.op1 as u64;
                Ok(z3::ast::BV::from_u64(ctx, value, 64).into())
            },
            OpKind::Neg => {
                let operand = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                if let Some(bv) = operand.as_bv() {
                    Ok(bv.bvneg().into())
                } else {
                    anyhow::bail!("Expected bitvector for negation")
                }
            },
            OpKind::Add => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvadd(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for addition")
                }
            },
            OpKind::Sub => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvsub(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for subtraction")
                }
            },
            OpKind::Mul => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvmul(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for multiplication")
                }
            },
            OpKind::Divu => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvudiv(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for unsigned division")
                }
            },
            OpKind::Div => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvsdiv(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for signed division")
                }
            },
            OpKind::Remu => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvurem(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for unsigned remainder")
                }
            },
            OpKind::Rem => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvsrem(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for signed remainder")
                }
            },
            OpKind::And => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvand(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for bitwise AND")
                }
            },
            OpKind::Or => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvor(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for bitwise OR")
                }
            },
            OpKind::Xor => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvxor(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for bitwise XOR")
                }
            },
            OpKind::Shl => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvshl(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for left shift")
                }
            },
            OpKind::Shr => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvlshr(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for logical right shift")
                }
            },
            OpKind::Sar => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvashr(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for arithmetic right shift")
                }
            },
            OpKind::Rotl => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    // Z3 rotate left by variable amount
                    Ok(lbv.bvrotl(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for rotate left")
                }
            },
            OpKind::Rotr => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    // Z3 rotate right by variable amount
                    Ok(lbv.bvrotr(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for rotate right")
                }
            },
            OpKind::Eq => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                Ok(left._eq(&right).into())
            },
            OpKind::Ne => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                Ok(left._eq(&right).not().into())
            },
            OpKind::Ltu => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvult(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for unsigned less than")
                }
            },
            OpKind::Leu => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvule(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for unsigned less than or equal")
                }
            },
            OpKind::Gtu => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvugt(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for unsigned greater than")
                }
            },
            OpKind::Geu => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvuge(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for unsigned greater than or equal")
                }
            },
            OpKind::Lt => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvslt(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for signed less than")
                }
            },
            OpKind::Le => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvsle(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for signed less than or equal")
                }
            },
            OpKind::Gt => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvsgt(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for signed greater than")
                }
            },
            OpKind::Ge => {
                let left = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op1 })?;
                let right = self.translate_expr_to_z3_with_ctx(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lbv), Some(rbv)) = (left.as_bv(), right.as_bv()) {
                    Ok(lbv.bvsge(&rbv).into())
                } else {
                    anyhow::bail!("Expected bitvectors for signed greater than or equal")
                }
            },
            _ => {
                // For unsupported operations, create a symbolic variable
                let var_name = format!("sym_{}", expr.opkind);
                Ok(z3::ast::BV::new_const(ctx, var_name, 64).into())
            }
        }
    }

    pub fn translate_expr_to_z3(&self, expr: &Expr) -> anyhow::Result<Dynamic> {
        match OpKind::try_from(expr.opkind)? {
            // Constants
            OpKind::IsConst => {
                // Extract constant value from op1 pointer cast
                let value = expr.op1 as u64;
                Ok(BV::from_u64(&self.ctx, value, 64).into())
            }
            
            // Symbolic variables
            OpKind::IsSymbolic => {
                let var_name = format!("sym_{:p}", expr);
                Ok(BV::new_const(&self.ctx, var_name.as_str(), 64).into())
            }
            
            // Unary operations
            OpKind::Neg => {
                if let Some(operand) = unsafe { expr.op1.as_ref() } {
                    let operand_z3 = self.translate_expr_to_z3(operand)?;
                    let operand_bv = operand_z3.as_bv().unwrap();
                    Ok(operand_bv.bvneg().into())
                } else {
                    let placeholder_name = format!("neg_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Not => {
                if let Some(operand) = unsafe { expr.op1.as_ref() } {
                    let operand_z3 = self.translate_expr_to_z3(operand)?;
                    let operand_bv = operand_z3.as_bv().unwrap();
                    Ok(operand_bv.bvnot().into())
                } else {
                    let placeholder_name = format!("not_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // Binary arithmetic operations
            OpKind::Add => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvadd(&right_bv).into())
                } else {
                    let placeholder_name = format!("add_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Sub => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvsub(&right_bv).into())
                } else {
                    let placeholder_name = format!("sub_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Mul => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvmul(&right_bv).into())
                } else {
                    let placeholder_name = format!("mul_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Mulu => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvmul(&right_bv).into())
                } else {
                    let placeholder_name = format!("mulu_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // Binary bitwise operations
            OpKind::And => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvand(&right_bv).into())
                } else {
                    let placeholder_name = format!("and_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Or => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvor(&right_bv).into())
                } else {
                    let placeholder_name = format!("or_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Xor => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvxor(&right_bv).into())
                } else {
                    let placeholder_name = format!("xor_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // Shift operations
            OpKind::Shl => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvshl(&right_bv).into())
                } else {
                    let placeholder_name = format!("shl_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Shr => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvlshr(&right_bv).into())
                } else {
                    let placeholder_name = format!("shr_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Sar => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvashr(&right_bv).into())
                } else {
                    let placeholder_name = format!("sar_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // Division operations
            OpKind::Div => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvsdiv(&right_bv).into())
                } else {
                    let placeholder_name = format!("div_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Divu => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvudiv(&right_bv).into())
                } else {
                    let placeholder_name = format!("divu_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // Remainder operations
            OpKind::Rem => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvsrem(&right_bv).into())
                } else {
                    let placeholder_name = format!("rem_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Remu => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvurem(&right_bv).into())
                } else {
                    let placeholder_name = format!("remu_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // Comparison operations (return Bool)
            OpKind::Eq => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv._eq(&right_bv).into())
                } else {
                    let placeholder_name = format!("eq_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            OpKind::Ne => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv._eq(&right_bv).not().into())
                } else {
                    let placeholder_name = format!("ne_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            // Additional comparison operations
            OpKind::Lt => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvslt(&right_bv).into())
                } else {
                    let placeholder_name = format!("lt_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            OpKind::Le => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvsle(&right_bv).into())
                } else {
                    let placeholder_name = format!("le_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            OpKind::Gt => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvsgt(&right_bv).into())
                } else {
                    let placeholder_name = format!("gt_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            OpKind::Ge => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvsge(&right_bv).into())
                } else {
                    let placeholder_name = format!("ge_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            // Unsigned comparison operations
            OpKind::Ltu => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvult(&right_bv).into())
                } else {
                    let placeholder_name = format!("ltu_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            OpKind::Leu => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvule(&right_bv).into())
                } else {
                    let placeholder_name = format!("leu_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            OpKind::Gtu => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvugt(&right_bv).into())
                } else {
                    let placeholder_name = format!("gtu_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            OpKind::Geu => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvuge(&right_bv).into())
                } else {
                    let placeholder_name = format!("geu_placeholder_{:p}", expr);
                    Ok(Bool::new_const(&self.ctx, placeholder_name.as_str()).into())
                }
            }
            
            // Rotation operations
            OpKind::Rotl => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvrotl(&right_bv).into())
                } else {
                    let placeholder_name = format!("rotl_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            OpKind::Rotr => {
                if let (Some(left_expr), Some(right_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let left_z3 = self.translate_expr_to_z3(left_expr)?;
                    let right_z3 = self.translate_expr_to_z3(right_expr)?;
                    let left_bv = left_z3.as_bv().unwrap();
                    let right_bv = right_z3.as_bv().unwrap();
                    Ok(left_bv.bvrotr(&right_bv).into())
                } else {
                    let placeholder_name = format!("rotr_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // i386-specific EFLAGS operations
            OpKind::EflagsAllAdd | OpKind::EflagsAllSub | OpKind::EflagsAllLogic | 
            OpKind::EflagsAllInc | OpKind::EflagsAllDec | OpKind::EflagsAllShl | 
            OpKind::EflagsAllSar | OpKind::EflagsAllMul | OpKind::EflagsAllBmilg => {
                if let (Some(dst_expr), Some(src1_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let dst_z3 = self.translate_expr_to_z3(dst_expr)?;
                    let src1_z3 = self.translate_expr_to_z3(src1_expr)?;
                    let dst_bv = dst_z3.as_bv().unwrap();
                    let src1_bv = src1_z3.as_bv().unwrap();
                    
                    // Extract width from op3 (stored as pointer cast)
                    let width = expr.op3 as usize;
                    let width = if width == 0 { 8 } else { width }; // Default to 8 bytes
                    
                    match i386::eflags_all_binary(&self.ctx, &dst_bv, &src1_bv, OpKind::try_from(expr.opkind)?, width) {
                        Ok(result) => Ok(result.into()),
                        Err(_) => {
                            let placeholder_name = format!("eflags_all_{:?}_{:p}", expr.opkind, expr);
                            Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                        }
                    }
                } else {
                    let placeholder_name = format!("eflags_all_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // i386 ternary EFLAGS operations (ADC/SBB variants)
            OpKind::EflagsAllAdcb | OpKind::EflagsAllAdcw | OpKind::EflagsAllAdcl | OpKind::EflagsAllAdcq |
            OpKind::EflagsAllSbbb | OpKind::EflagsAllSbbw | OpKind::EflagsAllSbbl | OpKind::EflagsAllSbbq => {
                if let (Some(dst_expr), Some(src1_expr), Some(src3_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() },
                    unsafe { expr.op3.as_ref() }
                ) {
                    let dst_z3 = self.translate_expr_to_z3(dst_expr)?;
                    let src1_z3 = self.translate_expr_to_z3(src1_expr)?;
                    let src3_z3 = self.translate_expr_to_z3(src3_expr)?;
                    let dst_bv = dst_z3.as_bv().unwrap();
                    let src1_bv = src1_z3.as_bv().unwrap();
                    let src3_bv = src3_z3.as_bv().unwrap();
                    
                    let width = match OpKind::try_from(expr.opkind)? {
                        OpKind::EflagsAllAdcb | OpKind::EflagsAllSbbb => 1,
                        OpKind::EflagsAllAdcw | OpKind::EflagsAllSbbw => 2,
                        OpKind::EflagsAllAdcl | OpKind::EflagsAllSbbl => 4,
                        OpKind::EflagsAllAdcq | OpKind::EflagsAllSbbq => 8,
                        _ => 8,
                    };
                    
                    match i386::eflags_all_ternary(&self.ctx, &dst_bv, &src1_bv, &src3_bv, OpKind::try_from(expr.opkind)?, width) {
                        Ok(result) => Ok(result.into()),
                        Err(_) => {
                            let placeholder_name = format!("eflags_ternary_{:?}_{:p}", expr.opkind, expr);
                            Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                        }
                    }
                } else {
                    let placeholder_name = format!("eflags_ternary_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // i386 ADCX/ADOX operations
            OpKind::EflagsAllAdcx | OpKind::EflagsAllAdox | OpKind::EflagsAllAdcox => {
                if let (Some(dst_expr), Some(src1_expr), Some(src2_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() },
                    unsafe { expr.op3.as_ref() }
                ) {
                    let dst_z3 = self.translate_expr_to_z3(dst_expr)?;
                    let src1_z3 = self.translate_expr_to_z3(src1_expr)?;
                    let src2_z3 = self.translate_expr_to_z3(src2_expr)?;
                    let dst_bv = dst_z3.as_bv().unwrap();
                    let src1_bv = src1_z3.as_bv().unwrap();
                    let src2_bv = src2_z3.as_bv().unwrap();
                    
                    match i386::eflags_all_adcxo(&self.ctx, &dst_bv, &src1_bv, &src2_bv, OpKind::try_from(expr.opkind)?) {
                        Ok(result) => Ok(result.into()),
                        Err(_) => {
                            let placeholder_name = format!("eflags_adcxo_{:?}_{:p}", expr.opkind, expr);
                            Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                        }
                    }
                } else {
                    let placeholder_name = format!("eflags_adcxo_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // i386 carry flag operations
            OpKind::EflagsCAdd | OpKind::EflagsCSub | OpKind::EflagsCShl | OpKind::EflagsCBmilg => {
                if let (Some(dst_expr), Some(src1_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let dst_z3 = self.translate_expr_to_z3(dst_expr)?;
                    let src1_z3 = self.translate_expr_to_z3(src1_expr)?;
                    let dst_bv = dst_z3.as_bv().unwrap();
                    let src1_bv = src1_z3.as_bv().unwrap();
                    
                    let width = expr.op3 as usize;
                    let width = if width == 0 { 8 } else { width };
                    
                    match i386::eflags_c_binary(&self.ctx, &dst_bv, &src1_bv, OpKind::try_from(expr.opkind)?, width) {
                        Ok(result) => Ok(result.into()),
                        Err(_) => {
                            let placeholder_name = format!("eflags_c_{:?}_{:p}", expr.opkind, expr);
                            Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                        }
                    }
                } else {
                    let placeholder_name = format!("eflags_c_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // i386 comparison operations
            OpKind::CmpEq | OpKind::CmpGt | OpKind::CmpGe | OpKind::CmpLt | OpKind::CmpLe => {
                if let (Some(op1_expr), Some(op2_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let op1_z3 = self.translate_expr_to_z3(op1_expr)?;
                    let op2_z3 = self.translate_expr_to_z3(op2_expr)?;
                    let op1_bv = op1_z3.as_bv().unwrap();
                    let op2_bv = op2_z3.as_bv().unwrap();
                    
                    let width = expr.op3 as usize;
                    let width = if width == 0 { 8 } else { width };
                    
                    match i386::handle_comparison(&self.ctx, &op1_bv, &op2_bv, OpKind::try_from(expr.opkind)?, width) {
                        Ok(result) => Ok(result.into()),
                        Err(_) => {
                            let placeholder_name = format!("cmp_{:?}_{:p}", expr.opkind, expr);
                            Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                        }
                    }
                } else {
                    let placeholder_name = format!("cmp_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // i386 MIN/MAX operations
            OpKind::Min | OpKind::Max => {
                if let (Some(op1_expr), Some(op2_expr)) = (
                    unsafe { expr.op1.as_ref() },
                    unsafe { expr.op2.as_ref() }
                ) {
                    let op1_z3 = self.translate_expr_to_z3(op1_expr)?;
                    let op2_z3 = self.translate_expr_to_z3(op2_expr)?;
                    let op1_bv = op1_z3.as_bv().unwrap();
                    let op2_bv = op2_z3.as_bv().unwrap();
                    
                    match i386::handle_min_max(&self.ctx, &op1_bv, &op2_bv, OpKind::try_from(expr.opkind)?) {
                        Ok(result) => Ok(result.into()),
                        Err(_) => {
                            let placeholder_name = format!("minmax_{:?}_{:p}", expr.opkind, expr);
                            Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                        }
                    }
                } else {
                    let placeholder_name = format!("minmax_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // i386 PMOVMSKB operation
            OpKind::Pmovmskb => {
                if let Some(op1_expr) = unsafe { expr.op1.as_ref() } {
                    let op1_z3 = self.translate_expr_to_z3(op1_expr)?;
                    let op1_bv = op1_z3.as_bv().unwrap();
                    
                    match i386::handle_pmovmskb(&self.ctx, &op1_bv) {
                        Ok(result) => Ok(result.into()),
                        Err(_) => {
                            let placeholder_name = format!("pmovmskb_{:p}", expr);
                            Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                        }
                    }
                } else {
                    let placeholder_name = format!("pmovmskb_placeholder_{:p}", expr);
                    Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
                }
            }
            
            // Placeholder for unsupported operations
            _ => {
                let placeholder_name = format!("unsupported_{:?}_{:p}", expr.opkind, expr);
                Ok(BV::new_const(&self.ctx, placeholder_name.as_str(), 64).into())
            }
        }
    }
    

    pub fn get_statistics(&self) -> (u64, u64, u64, u64, u64, u64, u64, u64, u64) {
        (
            self.sat_count,
            self.sat_time,
            self.unsat_count,
            self.unsat_time,
            self.unknown_count,
            self.unknown_time,
            self.translation_time,
            self.expr_visit_time,
            self.slice_reasoning_time,
        )
    }

    pub fn print_statistics(&self) {
        println!("SMT Solver Statistics:");
        println!("  SAT queries: {} (avg: {:.2}ms)", 
                 self.sat_count, 
                 if self.sat_count > 0 { self.sat_time as f64 / self.sat_count as f64 / 1000.0 } else { 0.0 });
        println!("  UNSAT queries: {} (avg: {:.2}ms)", 
                 self.unsat_count, 
                 if self.unsat_count > 0 { self.unsat_time as f64 / self.unsat_count as f64 / 1000.0 } else { 0.0 });
        println!("  UNKNOWN queries: {} (avg: {:.2}ms)", 
                 self.unknown_count, 
                 if self.unknown_count > 0 { self.unknown_time as f64 / self.unknown_count as f64 / 1000.0 } else { 0.0 });
        println!("  Translation time: {:.2}ms", self.translation_time as f64 / 1000.0);
        println!("  Expression visit time: {:.2}ms", self.expr_visit_time as f64 / 1000.0);
        println!("  Slice reasoning time: {:.2}ms", self.slice_reasoning_time as f64 / 1000.0);
    }

    pub fn check_sat(&mut self, expr: &Expr) -> anyhow::Result<SatResult> {
        let start_time = std::time::Instant::now();
        
        // Translate expression to Z3 and check satisfiability
        let z3_result = {
            let z3_expr = self.translate_expr_to_z3(expr)?;
            let solver = z3::Solver::new(&self.ctx);
            solver.assert(&z3_expr.as_bool().unwrap());
            solver.check()
        };
        
        let elapsed_time = start_time.elapsed().as_micros() as u64;
        
        // Update statistics
        match z3_result {
            SatResult::Sat => {
                self.sat_count += 1;
                self.sat_time += elapsed_time;
            }
            SatResult::Unsat => {
                self.unsat_count += 1;
                self.unsat_time += elapsed_time;
            }
            SatResult::Unknown => {
                self.unknown_count += 1;
                self.unknown_time += elapsed_time;
            }
        }
        
        Ok(z3_result)
    }
    
    pub fn get_model(&mut self, expr: &Expr) -> anyhow::Result<Option<z3::Model>> {
        let z3_expr = self.translate_expr_to_z3(expr)?;
        let solver = z3::Solver::new(&self.ctx);
        solver.assert(&z3_expr.as_bool().unwrap());
        
        match solver.check() {
            SatResult::Sat => {
                Ok(solver.get_model())
            }
            _ => Ok(None)
        }
    }

    pub fn negate_expr(&self, expr: &Expr) -> anyhow::Result<Expr> {
        // Create a negated expression
        let negated = Expr::new_unary(OpKind::Not, expr as *const Expr as *mut Expr);
        Ok(negated)
    }

    pub fn cleanup(&mut self) {
        // Cleanup resources
        if let Some(ref mut shared_mem) = self.shared_memory {
            // Shared memory cleanup is handled by Drop trait
        }
        if let Some(ref mut branch_cov) = self.branch_coverage {
            // Branch coverage cleanup is handled by Drop trait
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
    
    pub fn eval_expr(&self, _expr: &Expr) -> anyhow::Result<Option<u64>> {
        // Simplified model evaluation - would need full implementation
        Ok(None)
    }
}
