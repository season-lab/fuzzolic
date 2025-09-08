use std::os::raw::c_void;
use z3::ast::Bool;
use crate::solver::fuzzy::fuzzy_ffi::{
    fuzz_bridge_init,
    fuzz_bridge_check_light,
    fuzz_bridge_get_optimistic,
    fuzz_bridge_get_stats,
    raw_ast_from_bool,
    raw_ctx_from_bool,
    FuzzBridgeStats,
};

use crate::solver::SMTSolver;

impl SMTSolver {
    /// Notify the fuzzy engine about a newly added constraint (mirrors z3fuzz_notify_constraint)
    /// Note: does not initialize the fuzzy context; assumes it is already initialized elsewhere.
    pub fn fuzzy_notify_constraint(&self, constraint: &Bool) {
        if !self.fuzzy_enabled || self.fuzzy_ctx.is_null() { return; }
        unsafe {
            crate::solver::fuzzy::fuzzy_ffi::fuzz_bridge_notify_constraint(
                self.fuzzy_ctx,
                crate::solver::fuzzy::fuzzy_ffi::raw_ast_from_bool(constraint),
            );
        }
    }

    /// Initialize fuzzy context (once), using the same Z3 context as the Rust solver.
    fn init_fuzzy_once(&mut self) -> anyhow::Result<()> {
        if !self.fuzzy_enabled { return Ok(()); }
        if !self.fuzzy_ctx.is_null() { return Ok(()); }
        // Build a dummy Bool to extract Z3_context safely via raw helpers
        let true_b = Bool::from_bool(&self.ctx, true);
        let z3_ctx = unsafe { raw_ctx_from_bool(&true_b) };
        // Use configured fuzzy timeout
        let ptr = unsafe { fuzz_bridge_init(z3_ctx, self.fuzzy_timeout_ms) };
        self.fuzzy_ctx = ptr;
        Ok(())
    }

    /// Call C fuzzy solver fast checker via bridge: fuzz_bridge_check_light
    pub fn fuzzy_check_light(&mut self, fuzzy_query: &Bool, neg_query: &Bool) -> anyhow::Result<bool> {
        if !self.fuzzy_enabled { return Ok(false); }
        self.init_fuzzy_once()?;
        if self.fuzzy_ctx.is_null() { return Ok(false); }
        let query_raw = unsafe { raw_ast_from_bool(fuzzy_query) };
        let neg_raw = unsafe { raw_ast_from_bool(neg_query) };
        self.fuzzy_check_light_raw(query_raw, neg_raw)
    }

    /// Call the optimistic solver fallback (from C: z3fuzz_get_optimistic_sol)
    pub fn fuzzy_get_optimistic(&mut self) -> anyhow::Result<bool> {
        if !self.fuzzy_enabled { return Ok(false); }
        self.init_fuzzy_once()?;
        if self.fuzzy_ctx.is_null() { return Ok(false); }
        let mut proof: *const u8 = std::ptr::null();
        let mut proof_len: u64 = 0;
        let r = unsafe { fuzz_bridge_get_optimistic(self.fuzzy_ctx, &mut proof, &mut proof_len) };
        // Update basic stats from C
        self.pull_fuzzy_stats();
        Ok(r != 0)
    }

    /// Raw-pointer variant to avoid holding immutable borrows of Z3 context across the call.
    pub fn fuzzy_check_light_raw(&mut self, query_raw: *mut c_void, neg_raw: *mut c_void) -> anyhow::Result<bool> {
        if !self.fuzzy_enabled { return Ok(false); }
        self.init_fuzzy_once()?;
        if self.fuzzy_ctx.is_null() { return Ok(false); }
        let mut proof: *const u8 = std::ptr::null();
        let mut proof_len: u64 = 0;
        let r = unsafe { fuzz_bridge_check_light(self.fuzzy_ctx, query_raw, neg_raw, &mut proof, &mut proof_len) };
        // Update fuzzy stats from C after each call
        self.pull_fuzzy_stats();
        Ok(r != 0)
    }

    /// Const variant for fast fuzzy checks that avoids mutable borrows.
    /// Assumes the fuzzy context has been initialized earlier.
    pub fn fuzzy_check_light_raw_const(&self, query_raw: *mut c_void, neg_raw: *mut c_void) -> anyhow::Result<bool> {
        if !self.fuzzy_enabled { return Ok(false); }
        if self.fuzzy_ctx.is_null() { return Ok(false); }
        let mut proof: *const u8 = std::ptr::null();
        let mut proof_len: u64 = 0;
        let r = unsafe { fuzz_bridge_check_light(self.fuzzy_ctx, query_raw, neg_raw, &mut proof, &mut proof_len) };
        Ok(r != 0)
    }

    /// Pull fuzzy stats from C and update our Statistics
    fn pull_fuzzy_stats(&mut self) {
        if self.fuzzy_ctx.is_null() { return; }
        let mut s = FuzzBridgeStats::default();
        unsafe { fuzz_bridge_get_stats(self.fuzzy_ctx, &mut s as *mut FuzzBridgeStats) };
        // Map a subset into our stats. We only have num_evaluate->translation_time-ish proxy, and sat/timeout counts
        self.statistics.fuzzy_num_evaluate = s.num_evaluate as u64;
        self.statistics.fuzzy_num_sat = s.num_sat as u64;
        self.statistics.fuzzy_num_timeouts = s.num_timeouts as u64;
    }

    /// Public hook to refresh fuzzy stats before printing
    pub fn refresh_fuzzy_stats(&mut self) { self.pull_fuzzy_stats(); }
}
