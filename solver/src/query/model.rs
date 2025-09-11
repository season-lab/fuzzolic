use anyhow::Result;
use log::debug;
use crate::expressions::expression::{Query, Expr, ModelType};
use crate::solver::{SMTSolver, ConstraintRecord};
use crate::solver::concrete_eval::ConcreteEvaluator;

pub fn handle_model(solver: &mut SMTSolver, query: &Query, query_index: usize) -> Result<()> {
    debug!("Processing model query");
    let expr = if let Some(e) = query.query_expr() { e } else { return Ok(()); };
    let qidx = query_index;

    fn unpack4(x: u64) -> (u16, u16, u16, u16) {
        let a = (x & 0xFFFF) as u16;
        let b = ((x >> 16) & 0xFFFF) as u16;
        let c = ((x >> 32) & 0xFFFF) as u16;
        let d = ((x >> 48) & 0xFFFF) as u16;
        (a, b, c, d)
    }
    fn unpack2(x: u64) -> (u16, u16) {
        let a = (x & 0xFFFF) as u16;
        let b = ((x >> 16) & 0xFFFF) as u16;
        (a, b)
    }

    let model = query.model();
    match model {
        ModelType::Strcmp => {
            let s1 = if let Some(s) = expr.op1_ref() { s } else { anyhow::bail!("STRCMP missing s1") };
            let s2 = if let Some(s) = expr.op2_ref() { s } else { anyhow::bail!("STRCMP missing s2") };
            let packed = expr.get_op3_const().unwrap_or(0) as u64;
            let (res_u16, s1_len_u16, s2_len_u16, _n_u16) = unpack4(packed);
            let res = res_u16 as i32; // 0 means equal branch was taken
            let s1_len = s1_len_u16 as usize;
            let s2_len = s2_len_u16 as usize;
            let ctx = &solver.ctx;
            let z3_s1 = SMTSolver::translate_expression_static(ctx, s1)?;
            let z3_s2 = SMTSolver::translate_expression_static(ctx, s2)?;
            let mut evaluator = ConcreteEvaluator::new();
            let mut inputs_set: std::collections::HashSet<usize> = evaluator
                .get_inputs_expr(&z3_s1)
                .into_iter().map(|x| x as usize).collect();
            inputs_set.extend(evaluator.get_inputs_expr(&z3_s2).into_iter().map(|x| x as usize));
            let record = ConstraintRecord::StrideCmpEq {
                left_ptr: s1 as *const Expr,
                right_ptr: s2 as *const Expr,
                len: s1_len.min(s2_len),
                invert: res != 0,
            };
            solver.add_constraint_for_inputs(&inputs_set, qidx, record);
        }
        ModelType::Strlen => {
            let s1 = if let Some(s) = expr.op1_ref() { s } else { anyhow::bail!("STRLEN missing s1") };
            let packed = expr.get_op2_const().unwrap_or(0) as u64;
            let (s1_len_u16, n_u16) = unpack2(packed);
            let s1_len = s1_len_u16 as usize;
            let n = n_u16 as usize;
            let ctx = &solver.ctx;
            let z3_s1 = SMTSolver::translate_expression_static(ctx, s1)?;
            let mut evaluator = ConcreteEvaluator::new();
            let inputs_set: std::collections::HashSet<usize> = evaluator
                .get_inputs_expr(&z3_s1)
                .into_iter().map(|x| x as usize).collect();
            let record = ConstraintRecord::StrlenConstraint { expr_ptr: s1 as *const Expr, s1_len, n };
            solver.add_constraint_for_inputs(&inputs_set, qidx, record);
        }
        ModelType::Memcmp => {
            let s1 = if let Some(s) = expr.op1_ref() { s } else { anyhow::bail!("MEMCMP missing s1") };
            let s2 = if let Some(s) = expr.op2_ref() { s } else { anyhow::bail!("MEMCMP missing s2") };
            let packed = expr.get_op3_const().unwrap_or(0) as u64;
            let (res_u16, n_u16, _r2, _r3) = unpack4(packed);
            let res = res_u16 as i32;
            let n = n_u16 as usize;
            let ctx = &solver.ctx;
            let z3_s1 = SMTSolver::translate_expression_static(ctx, s1)?;
            let z3_s2 = SMTSolver::translate_expression_static(ctx, s2)?;
            let mut evaluator = ConcreteEvaluator::new();
            let mut inputs_set: std::collections::HashSet<usize> = evaluator
                .get_inputs_expr(&z3_s1)
                .into_iter().map(|x| x as usize).collect();
            inputs_set.extend(evaluator.get_inputs_expr(&z3_s2).into_iter().map(|x| x as usize));
            let record = ConstraintRecord::StrideCmpEq {
                left_ptr: s1 as *const Expr,
                right_ptr: s2 as *const Expr,
                len: n,
                invert: res != 0,
            };
            solver.add_constraint_for_inputs(&inputs_set, qidx, record);
        }
        ModelType::Memchr => {
            let s1 = if let Some(s) = expr.op1_ref() { s } else { anyhow::bail!("MEMCHR missing haystack") };
            let needle = expr.get_op2_const().unwrap_or(0) as u8;
            let packed = expr.get_op3_const().unwrap_or(0) as u64;
            let (_res, n_u16, _r2, _r3) = unpack4(packed);
            let n = n_u16 as usize;
            let ctx = &solver.ctx;
            let z3_s1 = SMTSolver::translate_expression_static(ctx, s1)?;
            let mut evaluator = ConcreteEvaluator::new();
            let inputs_set: std::collections::HashSet<usize> = evaluator
                .get_inputs_expr(&z3_s1)
                .into_iter().map(|x| x as usize).collect();
            let record = ConstraintRecord::MemchrConstraint { haystack_ptr: s1 as *const Expr, needle, n };
            solver.add_constraint_for_inputs(&inputs_set, qidx, record);
        }
        ModelType::Malloc => {
            let size = expr.get_op1_const().unwrap_or(0);
            let record = ConstraintRecord::MallocConstraint { size };
            let mut inputs = std::collections::HashSet::new();
            inputs.insert(0usize);
            solver.add_constraint_for_inputs(&inputs, qidx, record);
        }
        other => {
            debug!("Model {:?} not yet implemented in Rust; skipping", other);
        }
    }
    Ok(())
}
