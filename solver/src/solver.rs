use crate::expression::{Expr, DependencyGraph, SatResult};
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
        use crate::expression::OpKind;
        let op = OpKind::try_from(expr.opkind)?;
        match op {
            OpKind::Not => {
                let v = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(b) = v.as_bool() { Ok(b.not().into()) } else { Ok(v.as_bv().ok_or_else(|| anyhow::anyhow!("Not op1 not BV/bool"))?.bvnot().into()) }
            }
            OpKind::Neg => {
                let v = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                Ok(v.as_bv().ok_or_else(|| anyhow::anyhow!("Neg op1 not BV"))?.bvneg().into())
            }
            OpKind::IsConst => {
                let value = expr.op1 as u64;
                Ok(z3::ast::BV::from_u64(ctx, value, 64).into())
            }
            OpKind::Add => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Add lhs not BV"))?
                    .bvadd(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Add rhs not BV"))?)
                    .into())
            }
            OpKind::Sub => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Sub lhs not BV"))?
                    .bvsub(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Sub rhs not BV"))?)
                    .into())
            }
            OpKind::Mul => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Mul lhs not BV"))?
                    .bvmul(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Mul rhs not BV"))?)
                    .into())
            }
            OpKind::Mulu => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Mulu lhs not BV"))?
                    .bvmul(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Mulu rhs not BV"))?)
                    .into())
            }
            OpKind::Div => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Div lhs not BV"))?
                    .bvsdiv(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Div rhs not BV"))?)
                    .into())
            }
            OpKind::Divu => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Divu lhs not BV"))?
                    .bvudiv(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Divu rhs not BV"))?)
                    .into())
            }
            OpKind::Rem => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Rem lhs not BV"))?
                    .bvsrem(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Rem rhs not BV"))?)
                    .into())
            }
            OpKind::Remu => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Remu lhs not BV"))?
                    .bvurem(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Remu rhs not BV"))?)
                    .into())
            }
            OpKind::And => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
                    Ok(z3::ast::Bool::and(ctx, &[&lb, &rb]).into())
                } else {
                    Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("And lhs not BV/bool"))?
                        .bvand(&r.as_bv().ok_or_else(|| anyhow::anyhow!("And rhs not BV/bool"))?)
                        .into())
                }
            }
            OpKind::Or => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
                    Ok(z3::ast::Bool::or(ctx, &[&lb, &rb]).into())
                } else {
                    Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Or lhs not BV/bool"))?
                        .bvor(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Or rhs not BV/bool"))?)
                        .into())
                }
            }
            OpKind::Xor => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Xor lhs not BV"))?
                    .bvxor(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Xor rhs not BV"))?)
                    .into())
            }
            OpKind::Shl | OpKind::Sal => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Shl lhs not BV"))?
                    .bvshl(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Shl rhs not BV"))?)
                    .into())
            }
            OpKind::Shr => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Shr lhs not BV"))?
                    .bvlshr(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Shr rhs not BV"))?)
                    .into())
            }
            OpKind::Sar => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Sar lhs not BV"))?
                    .bvashr(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Sar rhs not BV"))?)
                    .into())
            }
            OpKind::Eq => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l._eq(&r).into())
            }
            OpKind::Ne => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l._eq(&r).not().into())
            }
            OpKind::Lt => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Lt lhs not BV"))?
                    .bvslt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Lt rhs not BV"))?)
                    .into())
            }
            OpKind::Le => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Le lhs not BV"))?
                    .bvsle(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Le rhs not BV"))?)
                    .into())
            }
            OpKind::Gt => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Gt lhs not BV"))?
                    .bvsgt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Gt rhs not BV"))?)
                    .into())
            }
            OpKind::Ge => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Ge lhs not BV"))?
                    .bvsge(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Ge rhs not BV"))?)
                    .into())
            }
            OpKind::Ltu => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Ltu lhs not BV"))?
                    .bvult(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Ltu rhs not BV"))?)
                    .into())
            }
            OpKind::Leu => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Leu lhs not BV"))?
                    .bvule(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Leu rhs not BV"))?)
                    .into())
            }
            OpKind::Gtu => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Gtu lhs not BV"))?
                    .bvugt(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Gtu rhs not BV"))?)
                    .into())
            }
            OpKind::Geu => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Geu lhs not BV"))?
                    .bvuge(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Geu rhs not BV"))?)
                    .into())
            }
            OpKind::Extract => {
                let v = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Extract op1 not BV"))?;
                let high = expr.op2 as u32;
                let low = expr.op3 as u32;
                Ok(bv.extract(high, low).into())
            }
            OpKind::Extract8 => {
                let v = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Extract8 op1 not BV"))?;
                Ok(bv.extract(7, 0).into())
            }
            OpKind::Concat => {
                let l = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let r = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(l.as_bv().ok_or_else(|| anyhow::anyhow!("Concat lhs not BV"))?
                    .concat(&r.as_bv().ok_or_else(|| anyhow::anyhow!("Concat rhs not BV"))?)
                    .into())
            }
            OpKind::Zext => {
                let v = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Zext op1 not BV"))?;
                let extend_bits = expr.op2 as u32;
                Ok(bv.zero_ext(extend_bits).into())
            }
            OpKind::Sext => {
                let v = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let bv = v.as_bv().ok_or_else(|| anyhow::anyhow!("Sext op1 not BV"))?;
                let extend_bits = expr.op2 as u32;
                Ok(bv.sign_ext(extend_bits).into())
            }
            // Keep placeholders for memory/symbolic ops used by higher layers
            OpKind::MemorySlice => {
                let base = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let size = expr.op2 as u64;
                let base_bv = base.as_bv().ok_or_else(|| anyhow::anyhow!("MemorySlice base not BV"))?;
                let name = format!("slice_{}_{}", base_bv.to_string(), size);
                Ok(z3::ast::BV::new_const(ctx, name, (size * 8) as u32).into())
            }
            OpKind::SymbolicLoad => {
                let addr = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let addr_bv = addr.as_bv().ok_or_else(|| anyhow::anyhow!("SymbolicLoad addr not BV"))?;
                let name = format!("load_{}", addr_bv.to_string());
                Ok(z3::ast::BV::new_const(ctx, name, 64).into())
            }
            OpKind::SymbolicStore => {
                let _addr = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let val = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                Ok(val)
            }
            OpKind::Rotl => {
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let amount = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(op_bv), Some(amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    Ok(op_bv.bvrotl(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Rotl operation")
                }
            }
            OpKind::Rotr => {
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let amount = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(op_bv), Some(amt_bv)) = (operand.as_bv(), amount.as_bv()) {
                    Ok(op_bv.bvrotr(&amt_bv).into())
                } else {
                    anyhow::bail!("Invalid operands for Rotr operation")
                }
            }
            // Optional Abs implementation (not part of OpKind currently)
            /* 36 => { // Abs (absolute value)
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
            } */
            OpKind::Min => {
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
            OpKind::Max => {
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
            OpKind::Nand => {
                let left = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                let right = Self::translate_expression_static(ctx, unsafe { &*expr.op2 })?;
                if let (Some(left_bv), Some(right_bv)) = (left.as_bv(), right.as_bv()) {
                    Ok(left_bv.bvand(&right_bv).bvnot().into())
                } else {
                    anyhow::bail!("Invalid operands for Nand operation")
                }
            }
            OpKind::Clz => { // count leading zeros (placeholder)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    let clz_name = format!("clz_{}", op_bv.to_string());
                    Ok(z3::ast::BV::new_const(ctx, clz_name, 64).into())
                } else {
                    anyhow::bail!("Invalid operand for Clz operation")
                }
            }
            OpKind::Ctz => { // count trailing zeros (placeholder)
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    let ctz_name = format!("ctz_{}", op_bv.to_string());
                    Ok(z3::ast::BV::new_const(ctx, ctz_name, 64).into())
                } else {
                    anyhow::bail!("Invalid operand for Ctz operation")
                }
            }
            OpKind::Bswap => {
                let operand = Self::translate_expression_static(ctx, unsafe { &*expr.op1 })?;
                if let Some(op_bv) = operand.as_bv() {
                    let size = op_bv.get_size();
                    if size % 8 != 0 { anyhow::bail!("Bswap requires byte-multiple width") }
                    let bytes = size / 8;
                    let mut acc: Option<z3::ast::BV> = None;
                    for i in 0..bytes {
                        let hi = (i + 1) * 8 - 1;
                        let lo = i * 8;
                        let byte = op_bv.extract(hi, lo);
                        acc = Some(match acc { None => byte, Some(a) => byte.concat(&a) });
                    }
                    Ok(acc.unwrap().into())
                } else {
                    anyhow::bail!("Invalid operand for Bswap operation")
                }
            }
            // i386-specific EFLAGS and comparison operations handled elsewhere if needed
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

