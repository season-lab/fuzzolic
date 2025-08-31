use crate::expression::{Expr, QueryType, DependencyGraph, SatResult};
use crate::shared_memory::SharedMemoryManager;
use crate::{BranchCoverage, FuzzySolver, Testcase};
use crate::concrete_eval::ConcreteEvaluator;
use z3::{Context, ast::Ast};
use anyhow::Result;
use log::info;

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
    shared_memory: Option<SharedMemoryManager>,
    branch_coverage: Option<BranchCoverage>,
    #[allow(dead_code)]
    _fuzzy_solver: Option<FuzzySolver>,
    statistics: Statistics,
    pub current_testcase: Option<Testcase>,
    symbols_sizes: Vec<u8>,
    symbols_count: usize,
    dependency_graph: DependencyGraph,
    concrete_evaluator: ConcreteEvaluator,
    #[allow(dead_code)]
    _expr_visit_time: u64,
    #[allow(dead_code)]
    _slice_reasoning_time: u64,
    translation_cache: std::cell::RefCell<std::collections::HashMap<u64, String>>,
}

impl SMTSolver {
    pub fn new(config: &crate::Config) -> Result<Self> {
        let z3_config = z3::Config::new();
        let ctx = Context::new(&z3_config);
        
        let shared_memory = if config.use_shared_memory {
            Some(SharedMemoryManager::new(config)?)
        } else {
            None
        };
        
        let branch_coverage = if config.use_branch_coverage {
            Some(BranchCoverage::new(config)?)
        } else {
            None
        };
        
        Ok(SMTSolver {
            ctx,
            shared_memory,
            branch_coverage,
            _fuzzy_solver: None,
            statistics: Statistics::default(),
            current_testcase: None,
            symbols_sizes: Vec::new(),
            symbols_count: 0,
            dependency_graph: DependencyGraph::new(),
            concrete_evaluator: ConcreteEvaluator::new(),
            _expr_visit_time: 0,
            _slice_reasoning_time: 0,
            translation_cache: std::cell::RefCell::new(std::collections::HashMap::new()),
        })
    }
    
    pub fn initialize(&mut self) -> Result<()> {
        // Initialize solver components
        // SharedMemoryManager doesn't have initialize method - it's initialized in constructor
        Ok(())
    }
    
    pub fn get_current_testcase(&self) -> Option<Vec<u8>> {
        self.current_testcase.as_ref().map(|t| t.data.clone())
    }
    
    pub fn print_statistics(&self) {
        println!("SMT Solver Statistics:");
        println!("  Queries processed: {}", self.statistics.queries_processed);
        println!("  Timeout count: {}", self.statistics.timeout_count);
        println!("  Translation time: {}ms", self.statistics.translation_time);
        println!("  Solving time: {}ms", self.statistics.solving_time);
        println!("  Cache hits: {}", self.statistics.cache_hits);
        println!("  Cache misses: {}", self.statistics.cache_misses);
    }
    
    pub fn solve_query(&mut self, expr: &Expr) -> Result<crate::expression::SatResult> {
        let z3_expr = self.translate_expression(expr)?;
        let solver = z3::Solver::new(&self.ctx);
        solver.assert(&z3_expr.as_bool().unwrap());
        
        match solver.check() {
            z3::SatResult::Sat => Ok(crate::expression::SatResult::Sat),
            z3::SatResult::Unsat => Ok(crate::expression::SatResult::Unsat),
            z3::SatResult::Unknown => Ok(crate::expression::SatResult::Unknown),
        }
    }
    
    pub fn process_shared_queries(&mut self) -> Result<crate::expression::SatResult> {
        // Process queries from shared memory
        if let Some(ref mut shared_mem) = self.shared_memory {
            if let Some(query) = shared_mem.get_next_query()? {
                // Process the query based on its type
                match query.query_type {
                    QueryType::Branch => {
                        // Handle branch queries
                        Ok(crate::expression::SatResult::Sat)
                    }
                    QueryType::Model => {
                        // Handle model queries  
                        Ok(crate::expression::SatResult::Sat)
                    }
                    _ => Ok(crate::expression::SatResult::Unknown)
                }
            } else {
                Ok(crate::expression::SatResult::Unknown)
            }
        } else {
            Ok(crate::expression::SatResult::Unknown)
        }
    }
    
    pub fn load_initial_testcase(&mut self) -> Result<bool> {
        // Load initial testcase if available
        if let Some(testcase) = &self.current_testcase {
            info!("Loaded initial testcase with {} bytes", testcase.data.len());
            Ok(true)
        } else {
            Ok(false)
        }
    }
    
    pub fn save_state(&self) -> Result<()> {
        // Save solver state and statistics
        info!("Saving solver state");
        if let Some(ref branch_coverage) = self.branch_coverage {
            branch_coverage.save_bitmaps()?;
        }
        Ok(())
    }

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
            // i386-specific EFLAGS and comparison operations (OpKind 50+)
            opkind if opkind >= 50 => {
                // Delegate to i386-specific translation
                crate::i386::smt_query_i386_to_z3(ctx, expr, 8)
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
            // Skip caching due to lifetime issues - translate directly
            // Proper caching would require string-based storage or Arc<> wrappers
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

