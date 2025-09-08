use std::os::raw::{c_void, c_int, c_uchar, c_ulong};

// Use opaque pointers for Z3 types to avoid depending on z3-sys here.
pub type Z3Context = *mut c_void;
pub type Z3Ast = *mut c_void;

extern "C" {
    // Opaque fuzzy context bridge managed in C to avoid layout issues.
    pub fn fuzz_bridge_init(z3_ctx: Z3Context, timeout_ms: u32) -> *mut c_void;
    pub fn fuzz_bridge_free(ctx: *mut c_void);
    pub fn fuzz_bridge_check_light(
        ctx: *mut c_void,
        query: Z3Ast,
        branch_condition: Z3Ast,
        proof: *mut *const c_uchar,
        proof_size: *mut c_ulong,
    ) -> c_int;
    pub fn fuzz_bridge_get_optimistic(
        ctx: *mut c_void,
        proof: *mut *const c_uchar,
        proof_size: *mut c_ulong,
    ) -> c_int;
    pub fn fuzz_bridge_get_stats(ctx: *mut c_void, out_stats: *mut FuzzBridgeStats);
    pub fn fuzz_bridge_notify_constraint(ctx: *mut c_void, constraint: Z3Ast);
}

// Extremely scoped, unsafe helpers to extract raw Z3 pointers from z3 crate types.
// These rely on the z3 crate's internal layout for Bool/Ast/Context and must be
// kept in sync with z3 = "0.12". They are used ONLY for FFI calls to the C fuzzy solver.

#[repr(C)]
struct ContextRepr {
    z3_ctx: Z3Context,
}

#[repr(C)]
struct AstRepr {
    ctx: *const ContextRepr,
    z3_ast: Z3Ast,
}

#[repr(C)]
struct BoolRepr {
    ast: AstRepr,
}

pub unsafe fn raw_ctx_from_bool(b: &z3::ast::Bool) -> Z3Context {
    let brepr = &*(b as *const _ as *const BoolRepr);
    (*brepr.ast.ctx).z3_ctx
}

pub unsafe fn raw_ast_from_bool(b: &z3::ast::Bool) -> Z3Ast {
    let brepr = &*(b as *const _ as *const BoolRepr);
    brepr.ast.z3_ast
}

#[repr(C)]
#[derive(Default, Debug, Clone, Copy)]
pub struct FuzzBridgeStats {
    pub num_evaluate: c_ulong,
    pub num_sat: c_ulong,
    pub num_timeouts: c_ulong,
}
