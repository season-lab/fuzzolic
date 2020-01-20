#ifndef SOLVER_H
#define SOLVER_H

#include <stdint.h>
#include <unistd.h>

#include <z3.h>
#define Z3_VERSION 451

#define USE_COLOR
#include "debug.h"

#include "../tracer/tcg/symbolic/symbolic-struct.h"

Z3_ast smt_query_to_z3(Expr* query, uintptr_t is_const, size_t width);
void   smt_print_ast_sort(Z3_ast e);
Z3_ast smt_new_const(uint64_t value, size_t n_bits);
Z3_ast smt_new_symbol(const char* name, size_t n_bits, Expr* e);
Z3_ast smt_bv_extract(Z3_ast e, size_t width);
Z3_ast smt_to_bv(Z3_ast e);
Z3_ast smt_to_bv_n(Z3_ast e, size_t width);

#define CONST_EXTRACT(c, width) (-1)

#endif // SOLVER_H