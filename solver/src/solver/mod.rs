pub mod fuzzy;
pub mod translate;
pub mod constraints;
pub mod i386;
pub mod concrete_eval;

use anyhow::Result;
use z3::Context;
use crate::coverage::branch_coverage::BranchCoverage;
use crate::expressions::expression::{Expr, DependencyGraph};
use crate::utils::statistics::Statistics;
use crate::utils::testcase::Testcase;
use crate::expressions::expression;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

pub use self::constraints::ConstraintRecord;

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
    pub(crate) branch_coverage: Option<BranchCoverage>,
    pub(crate) statistics: Statistics,
    pub current_testcase: Option<Testcase>,
    pub(crate) dependency_graph: DependencyGraph,
    pub(crate) dep_bool_ids: RefCell<HashSet<usize>>,
    pub(crate) dep_nonbool_ids: RefCell<HashSet<usize>>,
    // Fuzzy solver interop
    pub(crate) fuzzy_enabled: bool,
    pub(crate) fuzzy_timeout_ms: u32,
    pub(crate) fuzzy_ctx: *mut std::os::raw::c_void,
    // Cached constraints by input id and by query index
    pub(crate) constraints_by_input: RefCell<HashMap<usize, Vec<ConstraintRecord>>>,
    pub(crate) constraints_by_query: RefCell<HashMap<usize, ConstraintRecord>>,
}

impl SMTSolver {
    pub fn new(config: &crate::Config) -> Result<Self> {
        let z3_cfg = z3::Config::new();
        let ctx = Context::new(&z3_cfg);

        let branch_coverage = if config.use_branch_coverage {
            Some(BranchCoverage::new(config)?)
        } else { None };

        Ok(SMTSolver {
            ctx,
            branch_coverage,
            statistics: Statistics::default(),
            current_testcase: None,
            dependency_graph: DependencyGraph::new(),
            dep_bool_ids: RefCell::new(HashSet::new()),
            dep_nonbool_ids: RefCell::new(HashSet::new()),
            fuzzy_enabled: config.use_fuzzy_solver,
            fuzzy_timeout_ms: config.fuzzy_timeout_ms(),
            fuzzy_ctx: std::ptr::null_mut(),
            constraints_by_input: RefCell::new(HashMap::new()),
            constraints_by_query: RefCell::new(HashMap::new()),
        })
    }

    pub fn initialize(&mut self) -> Result<()> {
        Ok(())
    }

    /// Record dependency information for an expression into the dependency graph.
    pub fn add_dependency_for_expr(&mut self, expr: &Expr) -> Result<()> {
        let z3_expr = Self::translate_expression_static(&self.ctx, expr)?;
        let mut evaluator = concrete_eval::ConcreteEvaluator::new();
        let inputs = evaluator.get_inputs_expr(&z3_expr);
        let expr_id = expr as *const Expr as usize;
        for input_id in inputs { self.dependency_graph.add_dependency(input_id as usize, expr_id); }
        Ok(())
    }

    /// Retrieve merged dependencies information for a set of input IDs.
    pub fn get_deps_for_inputs(&self, inputs: &HashSet<usize>) -> expression::Dependency {
        self.dependency_graph.merge_dependencies(inputs)
    }

    /// Mark an expression ID as Bool-producing.
    pub(crate) fn mark_dep_bool_id(&self, id: usize) {
        self.dep_bool_ids.borrow_mut().insert(id);
        self.dep_nonbool_ids.borrow_mut().remove(&id);
    }

    /// Mark an expression ID as non-Bool-producing.
    pub(crate) fn mark_dep_nonbool_id(&self, id: usize) {
        self.dep_nonbool_ids.borrow_mut().insert(id);
        self.dep_bool_ids.borrow_mut().remove(&id);
    }

    /// Check known kind caches.
    pub fn is_dep_bool_id(&self, id: usize) -> bool { self.dep_bool_ids.borrow().contains(&id) }
    pub fn is_dep_nonbool_id(&self, id: usize) -> bool { self.dep_nonbool_ids.borrow().contains(&id) }

    /// Ensure we know whether an expression is Bool-producing. Returns true if Bool.
    pub fn ensure_dep_is_bool(&self, expr: &Expr) -> bool {
        let id = expr as *const Expr as usize;
        if self.is_dep_bool_id(id) { return true; }
        if self.is_dep_nonbool_id(id) { return false; }
        match Self::translate_expression_static(&self.ctx, expr) {
            Ok(ast) => {
                if ast.as_bool().is_some() { self.mark_dep_bool_id(id); true } else { self.mark_dep_nonbool_id(id); false }
            }
            Err(_) => { self.mark_dep_nonbool_id(id); false }
        }
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
        println!("  Fuzzy num_evaluate: {}", self.statistics.fuzzy_num_evaluate);
        println!("  Fuzzy num_sat: {}", self.statistics.fuzzy_num_sat);
        println!("  Fuzzy num_timeouts: {}", self.statistics.fuzzy_num_timeouts);
    }

    pub fn save_bitmaps(&self) -> anyhow::Result<()> {
        if let Some(ref branch_cov) = self.branch_coverage { branch_cov.save_bitmaps()?; }
        Ok(())
    }
}

impl Drop for SMTSolver {
    fn drop(&mut self) {
        if !self.fuzzy_ctx.is_null() {
            unsafe { crate::solver::fuzzy::fuzzy_ffi::fuzz_bridge_free(self.fuzzy_ctx) };
            self.fuzzy_ctx = std::ptr::null_mut();
        }
    }
}
