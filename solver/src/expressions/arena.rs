use std::cell::RefCell;

use crate::expressions::expression::Expr;

pub struct ExprArena {
    nodes: Vec<Box<Expr>>,
}

impl ExprArena {
    pub fn new() -> Self {
        Self { nodes: Vec::with_capacity(1024) }
    }
    /// Allocate an Expr in the arena and return a stable raw pointer to it.
    pub fn alloc(&mut self, expr: Expr) -> *mut Expr {
        self.nodes.push(Box::new(expr));
        let last: *mut Expr = &mut **self.nodes.last_mut().unwrap();
        last
    }
    pub fn len(&self) -> usize { self.nodes.len() }
}

thread_local! {
    pub static TLS_ARENA: RefCell<Option<ExprArena>> = RefCell::new(None);
}

/// Enter a TLS arena scope. Returns true if this call created the arena (and thus must be exited).
pub fn enter_tls_arena() -> bool {
    TLS_ARENA.with(|cell| {
        if cell.borrow().is_none() {
            *cell.borrow_mut() = Some(ExprArena::new());
            true
        } else { false }
    })
}

/// Exit a TLS arena scope created by enter_tls_arena().
pub fn exit_tls_arena(created: bool) {
    if created {
        TLS_ARENA.with(|cell| {
            cell.borrow_mut().take();
        });
    }
}

/// Try to allocate in the TLS arena if present. Returns None if no arena is set.
pub fn tls_alloc_opt(expr: Expr) -> Option<*mut Expr> {
    TLS_ARENA.with(|cell| {
        if let Some(arena) = cell.borrow_mut().as_mut() {
            Some(arena.alloc(expr))
        } else { None }
    })
}

pub struct ArenaScope { created: bool }

impl ArenaScope {
    pub fn enter() -> Self { Self { created: enter_tls_arena() } }
}

impl Drop for ArenaScope {
    fn drop(&mut self) { exit_tls_arena(self.created); }
}
