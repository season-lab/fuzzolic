use anyhow::Result;
use log::{debug, warn};
use crate::expressions::expression::{Query, Expr, OpKind};
use crate::solver::SMTSolver;
use crate::query::memory_slice::MemorySliceReasoner;
use crate::utils::config::Config;
use crate::solver::concrete_eval::ConcreteEvaluator;
use z3::ast::Ast;
use crate::query::memory_slice;

pub fn handle_consistency(solver: &mut SMTSolver, query: &Query) -> Result<()> {
    if query.query.is_null() { return Ok(()); }
    let expr = unsafe { &*query.query };
    // Consistency expression is in op1; concrete expected value in op2
    let target = if expr.op1.is_null() { anyhow::bail!("Consistency expr missing op1") } else { unsafe { &*expr.op1 } };
    let expected = expr.get_op2_const().unwrap_or(0) as u64;

    let ctx = &solver.ctx;
    let z3_e = SMTSolver::translate_expression_static(ctx, target)?;

    // Evaluate using current testcase bytes if available
    let input_bytes: Vec<u8> = solver.get_current_testcase().unwrap_or_default();
    let mut evaluator = ConcreteEvaluator::new();
    let (solution, _cached) = evaluator.conc_eval(ctx, &z3_e, &input_bytes, &std::collections::HashMap::new())?;

    if solution == expected {
        debug!("Consistency check OK at 0x{:x}", query.address as u64);
    } else {
        warn!(
            "Consistency check FAIL at 0x{:x}: expected=0x{:x} solution=0x{:x}",
            query.address as u64,
            expected,
            solution
        );
    }
    Ok(())
}

pub fn handle_mem_concretization(solver: &mut SMTSolver, expr: &Expr) -> Result<()> {
    // Target expression is in op1; concrete value in op2
    let target = if expr.op1.is_null() { anyhow::bail!("Mem concretization missing op1") } else { unsafe { &*expr.op1 } };
    let conc_val = expr.get_op2_const().unwrap_or(0) as u64;
    // Record deps first to avoid borrowing conflicts
    let _ = solver.add_dependency_for_expr(target);
    let ctx = &solver.ctx;
    let z3_dyn = SMTSolver::translate_expression_static(ctx, target)?;
    if let Some(bv) = z3_dyn.as_bv() {
        let width = bv.get_size();
        let val = z3::ast::BV::from_u64(ctx, conc_val, width);
        let eq = bv._eq(&val);
        solver.fuzzy_notify_constraint(&eq);
    } else if let Some(b) = z3_dyn.as_bool() {
        let eq = if conc_val == 0 { b.not() } else { b };
        solver.fuzzy_notify_constraint(&eq);
    } else {
        warn!("Mem concretization target not BV/Bool; skipping");
    }
    Ok(())
}

pub fn handle_slice(_solver: &mut SMTSolver, reasoner: &mut MemorySliceReasoner, _config: &Config, query: &Query) -> Result<()> {
    // Prefer the C-style layout: q->query points to the slice node; the next node is the s_load descriptor.
    if query.query.is_null() {
        // Fallback to args if no expression pointer is provided
        let slice_args = unsafe { &query.args.args8 };
        let addr_conc = slice_args.arg1 as u64;
        let size = slice_args.arg2 as usize;
        let load_id = slice_args.arg3 as u64;
        debug!("[slice:fallback] addr={:x}, size={}, load_id={}", addr_conc, size, load_id);
        reasoner.process_slice_access(addr_conc, size, load_id)?;
        return Ok(());
    }

    // SAFETY: query.query is a valid pointer to an Expr in shared memory
    let slice_node = unsafe { &*query.query };
    let opkind = OpKind::try_from(slice_node.opkind)?;
    // The C code handles MEMORY_SLICE and MEMORY_SLICE_ACCESS similarly and inspects the adjacent s_load node.
    if opkind != OpKind::MemorySlice && opkind != OpKind::MemorySliceAccess {
        anyhow::bail!("Unexpected opkind for slice query: {:?}", opkind);
    }

    // Extract concrete address and s_load_id from slice node constants
    let addr_conc = if slice_node.op2_is_const != 0 { slice_node.op2 as u64 } else { 0 };
    let s_load_id = if slice_node.op3_is_const != 0 { slice_node.op3 as u64 } else { 0 };

    // Adjacent symbolic-load descriptor: (q->query + 1)
    let s_load_ptr = unsafe { query.query.add(1) };
    if s_load_ptr.is_null() { anyhow::bail!("Missing s_load descriptor after slice node"); }
    let s_load = unsafe { &*s_load_ptr };
    if OpKind::try_from(s_load.opkind)? != OpKind::IsSymbolic {
        anyhow::bail!("s_load descriptor not IS_SYMBOLIC");
    }
    // Validate s_load_id
    if !(s_load.op1_is_const != 0 && (s_load.op1 as u64) == s_load_id) {
        anyhow::bail!("s_load id mismatch: expected {} got {}", s_load_id, s_load.op1 as u64);
    }
    let s_load_size = if s_load.op2_is_const != 0 { s_load.op2 as usize } else { 0 };

    // Optional concrete value for MEMORY_SLICE_ACCESS
    let mut concrete_bytes: Option<[u8; memory_slice::SLICE_SIZE]> = None;
    if opkind == OpKind::MemorySliceAccess && s_load.op3_is_const != 0 {
        let val = s_load.op3 as u64;
        let mut data = [0u8; memory_slice::SLICE_SIZE];
        let n = s_load_size.min(memory_slice::SLICE_SIZE);
        for i in 0..n { data[i] = ((val >> (8 * i)) & 0xFF) as u8; }
        concrete_bytes = Some(data);
    }

    debug!(
        "[slice] addr={:x} size={} load_id={} op={:?} concrete={}",
        addr_conc,
        s_load_size,
        s_load_id,
        opkind,
        concrete_bytes.is_some()
    );

    // Record the slice and mapping in the reasoner
    if let Some(bytes) = concrete_bytes {
        reasoner.add_slice(addr_conc, bytes);
    }
    reasoner.add_input_slice(addr_conc, s_load_id as usize);
    // Also notify via the unified API
    reasoner.process_slice_access(addr_conc, s_load_size, s_load_id)?;

    Ok(())
}
