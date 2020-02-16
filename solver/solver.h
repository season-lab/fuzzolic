#ifndef SOLVER_H
#define SOLVER_H

#include <stdint.h>
#include <unistd.h>

#include <gmodule.h>

#include <z3.h>
#define Z3_VERSION 451

#define USE_COLOR
#include "debug.h"

#include "../tracer/tcg/symbolic/symbolic-struct.h"

typedef enum ExprAnnotationType {
    COSTANT_AND,
} ExprAnnotationType;

typedef struct ExprAnnotation {
    ExprAnnotationType type;
    uintptr_t          value;
    void*              result;
} ExprAnnotation;

Z3_ast smt_query_to_z3(Expr* query, uintptr_t is_const, size_t width, GHashTable* inputs);
void   smt_print_ast_sort(Z3_ast e);
Z3_ast smt_new_const(uint64_t value, size_t n_bits);
Z3_ast smt_new_symbol(uintptr_t id, const char* name, size_t n_bits, Expr* e);
Z3_ast smt_bv_extract(Z3_ast e, size_t width);
Z3_ast smt_to_bv(Z3_ast e);
Z3_ast smt_to_bv_n(Z3_ast e, size_t width);
void smt_bv_resize(Z3_ast* a, Z3_ast* b, ssize_t size);

void            add_expr_annotation(Expr* e, ExprAnnotation* ea);
ExprAnnotation* get_expr_annotation(Expr* e);

#endif // SOLVER_H