#ifndef SOLVER_I386_H
#define SOLVER_I386_H

#include <z3.h>
#include <unistd.h>

#define XMM_BITES 16

Z3_ast smt_query_i386_to_z3(Z3_context ctx, Expr* query, uintptr_t is_const,
                            size_t width);

#endif // SOLVER_I386_H