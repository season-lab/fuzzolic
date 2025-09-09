use crate::expressions::expression::Expr;
use crate::solver::SMTSolver;
use z3::ast::{Ast, Bool, BV};

#[derive(Clone)]
pub enum ConstraintRecord {
    /// Equality between a BV expression and a concrete value
    EqBV { expr_ptr: *const Expr, value: u64 },
    /// Equality of two BV expressions over the first `len` bytes (little-endian). If `invert` is true, negate the equality.
    StrideCmpEq { left_ptr: *const Expr, right_ptr: *const Expr, len: usize, invert: bool },
    /// STRLEN-style constraint: all bytes [0..s1_len-1] are non-zero, and optionally byte at s1_len is zero depending on `n`.
    StrlenConstraint { expr_ptr: *const Expr, s1_len: usize, n: usize },
    /// MEMCHR-style constraint: in the first `n` bytes of `haystack`, there exists an index with value == `needle`.
    MemchrConstraint { haystack_ptr: *const Expr, needle: u8, n: usize },
    /// MALLOC-style constraint: record requested allocation size; cached so future expressions can depend on it.
    /// In C this influences later reasonings; in Rust we keep it to attach to inputs.
    MallocConstraint { size: usize },
}

impl SMTSolver {
    /// Record a constraint both by query index and for each input id involved (ports update_and_add_deps_to_solver behavior for constraints).
    pub fn add_constraint_for_inputs(
        &self,
        inputs: &std::collections::HashSet<usize>,
        query_idx: usize,
        record: ConstraintRecord,
    ) {
        // Save by query index (override if exists)
        self.constraints_by_query
            .borrow_mut()
            .insert(query_idx, record.clone());
        // Save under each input id
        let mut map = self.constraints_by_input.borrow_mut();
        for &inp in inputs {
            map.entry(inp).or_default().push(record.clone());
        }
    }

    /// Build constraint Bool ASTs for all constraints associated with the provided inputs.
    pub fn get_constraint_bools_for_inputs(
        &self,
        inputs: &std::collections::HashSet<usize>,
    ) -> Vec<Bool> {
        let mut bools = Vec::new();
        let map = self.constraints_by_input.borrow();
        for &inp in inputs {
            if let Some(records) = map.get(&inp) {
                for rec in records {
                    match rec {
                        ConstraintRecord::EqBV { expr_ptr, value } => {
                            if Expr::with_ref_from_ptr(*expr_ptr, |e| {
                                if let Ok(dyn_ast) = Self::translate_expression_static(&self.ctx, e) {
                                    if let Some(bv) = dyn_ast.as_bv() {
                                        let width = bv.get_size();
                                        let v = BV::from_u64(&self.ctx, *value, width);
                                        let eq = bv._eq(&v);
                                        bools.push(eq);
                                    }
                                }
                            }).is_none() { continue; }
                        }
                        ConstraintRecord::StrideCmpEq { left_ptr, right_ptr, len, invert } => {
                            let mut pushed = false;
                            let left_ok = Expr::with_ref_from_ptr(*left_ptr, |le| {
                                let right_ok = Expr::with_ref_from_ptr(*right_ptr, |re| {
                                    if let (Ok(ld), Ok(rd)) = (
                                        Self::translate_expression_static(&self.ctx, le),
                                        Self::translate_expression_static(&self.ctx, re),
                                    ) {
                                        if let (Some(lbv), Some(rbv)) = (ld.as_bv(), rd.as_bv()) {
                                            let mut b = self.build_stride_cmpeq_bool(&lbv, &rbv, *len);
                                            if *invert { b = b.not(); }
                                            bools.push(b);
                                            pushed = true;
                                        }
                                    }
                                });
                                if right_ok.is_none() { /* no-op */ }
                            });
                            if left_ok.is_none() || !pushed { continue; }
                        }
                        ConstraintRecord::StrlenConstraint { expr_ptr, s1_len, n } => {
                            if Expr::with_ref_from_ptr(*expr_ptr, |e| {
                                if let Ok(dyn_ast) = Self::translate_expression_static(&self.ctx, e) {
                                    if let Some(bv) = dyn_ast.as_bv() {
                                        let b = self.build_strlen_bool(&bv, *s1_len, *n);
                                        bools.push(b);
                                    }
                                }
                            }).is_none() { continue; }
                        }
                        ConstraintRecord::MemchrConstraint { haystack_ptr, needle, n } => {
                            if Expr::with_ref_from_ptr(*haystack_ptr, |e| {
                                if let Ok(dyn_ast) = Self::translate_expression_static(&self.ctx, e) {
                                    if let Some(bv) = dyn_ast.as_bv() {
                                        let b = self.build_memchr_bool(&bv, *needle, *n);
                                        bools.push(b);
                                    }
                                }
                            }).is_none() { continue; }
                        }
                        ConstraintRecord::MallocConstraint { .. } => {
                            // No direct Bool constraint to assert here; kept for parity.
                        }
                    }
                }
            }
        }
        bools
    }

    /// Build a Bool asserting equality between two byte vectors over the first `len` bytes.
    fn build_stride_cmpeq_bool<'a>(&'a self, s1: &BV<'a>, s2: &BV<'a>, len: usize) -> Bool<'a> {
        use z3::ast::Bool as Z3Bool;
        if len == 0 { return Z3Bool::from_bool(&self.ctx, true); }
        let total_bits = len * 8;
        let mut start = 0;
        let mut acc: Option<Bool<'a>> = None;
        while start < total_bits {
            let end = (start + 64).min(total_bits);
            let a = s1.extract(end as u32 - 1, start as u32);
            let b = s2.extract(end as u32 - 1, start as u32);
            let eq = a._eq(&b);
            acc = Some(match acc { None => eq, Some(prev) => Z3Bool::and(&self.ctx, &[&prev, &eq]) });
            start = end;
        }
        acc.unwrap()
    }

    /// Build STRLEN-style constraint as in C smt_model_expr for MODEL_STRLEN.
    fn build_strlen_bool<'a>(&'a self, s: &BV<'a>, s1_len: usize, n: usize) -> Bool<'a> {
        use z3::ast::Bool as Z3Bool;
        let mut acc: Option<Bool<'a>> = None;
        // All bytes before s1_len must be non-zero
        for i in 0..s1_len {
            let byte = s.extract((8 * (i + 1) - 1) as u32, (8 * i) as u32);
            let neq_zero = byte._eq(&BV::from_u64(&self.ctx, 0, 8)).not();
            acc = Some(match acc { None => neq_zero, Some(prev) => Z3Bool::and(&self.ctx, &[&prev, &neq_zero]) });
        }
        // If n == 0 or s1_len < n, enforce zero terminator at position s1_len
        if n == 0 || s1_len < n {
            let byte = s.extract((8 * (s1_len + 1) - 1) as u32, (8 * s1_len) as u32);
            let eq_zero = byte._eq(&BV::from_u64(&self.ctx, 0, 8));
            acc = Some(match acc { None => eq_zero, Some(prev) => Z3Bool::and(&self.ctx, &[&prev, &eq_zero]) });
        }
        acc.unwrap_or_else(|| Z3Bool::from_bool(&self.ctx, true))
    }

    /// Build MEMCHR-style constraint: OR over i in [0..n) of (extract byte i == needle)
    fn build_memchr_bool<'a>(&'a self, s: &BV<'a>, needle: u8, n: usize) -> Bool<'a> {
        use z3::ast::Bool as Z3Bool;
        if n == 0 { return Z3Bool::from_bool(&self.ctx, false); }
        let mut acc: Option<Bool<'a>> = None;
        let needle_bv = BV::from_u64(&self.ctx, needle as u64, 8);
        for i in 0..n {
            let byte = s.extract((8 * (i + 1) - 1) as u32, (8 * i) as u32);
            let eq = byte._eq(&needle_bv);
            acc = Some(match acc { None => eq, Some(prev) => Z3Bool::or(&self.ctx, &[&prev, &eq]) });
        }
        acc.unwrap()
    }
}
