#include "fuzzy-sat/z3-fuzzy.h"
#include <stdlib.h>
#include <stdint.h>

// Opaque bridge context wrapping the C fuzzy context
typedef struct fuzz_bridge_s {
    fuzzy_ctx_t ctx;
} fuzz_bridge_t;

// Minimal stats surface for Rust
typedef struct fuzz_bridge_stats_s {
    unsigned long num_evaluate;
    unsigned long num_sat;
    unsigned long num_timeouts;
} fuzz_bridge_stats_t;

void* fuzz_bridge_init(Z3_context z3_ctx, unsigned timeout_ms) {
    fuzz_bridge_t* b = (fuzz_bridge_t*)malloc(sizeof(fuzz_bridge_t));
    if (!b) return NULL;
    z3fuzz_init(&b->ctx, z3_ctx, NULL, NULL, NULL, timeout_ms);
    return (void*)b;
}

void fuzz_bridge_free(void* p) {
    if (!p) return;
    fuzz_bridge_t* b = (fuzz_bridge_t*)p;
    z3fuzz_free(&b->ctx);
    free(b);
}

int fuzz_bridge_check_light(void* p,
                            Z3_ast query,
                            Z3_ast branch_condition,
                            const unsigned char** proof,
                            unsigned long* proof_size) {
    if (!p) return 0;
    fuzz_bridge_t* b = (fuzz_bridge_t*)p;
    return z3fuzz_query_check_light(&b->ctx, query, branch_condition, proof, proof_size);
}

int fuzz_bridge_get_optimistic(void* p,
                               const unsigned char** proof,
                               unsigned long* proof_size) {
    if (!p) return 0;
    fuzz_bridge_t* b = (fuzz_bridge_t*)p;
    return z3fuzz_get_optimistic_sol(&b->ctx, proof, proof_size);
}

void fuzz_bridge_get_stats(void* p, fuzz_bridge_stats_t* out_stats) {
    if (!p || !out_stats) return;
    fuzz_bridge_t* b = (fuzz_bridge_t*)p;
    out_stats->num_evaluate = b->ctx.stats.num_evaluate;
    out_stats->num_sat = b->ctx.stats.num_sat;
    out_stats->num_timeouts = b->ctx.stats.num_timeouts;
}

void fuzz_bridge_notify_constraint(void* p, Z3_ast constraint) {
    if (!p) return;
    fuzz_bridge_t* b = (fuzz_bridge_t*)p;
    z3fuzz_notify_constraint(&b->ctx, constraint);
}
