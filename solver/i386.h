#ifndef SOLVER_I386_H
#define SOLVER_I386_H

#include <z3.h>
#include <unistd.h>

#define XMM_BITES 16

/* eflags masks */
#define CC_C    0x0001
#define CC_P    0x0004
#define CC_A    0x0010
#define CC_Z    0x0040
#define CC_S    0x0080
#define CC_O    0x0800

#define SIGN_MASK (1 << ((width * 8) - 1))

Z3_ast smt_query_i386_to_z3(Z3_context ctx, Expr* query, uintptr_t is_const,
                            size_t width);

#endif // SOLVER_I386_H