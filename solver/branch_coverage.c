#include "solver.h"

extern Config config;

#define XXH_STATIC_LINKING_ONLY
#include "xxHash/xxhash.h"

#if BRANCH_COVERAGE == QSYM
static uint8_t branch_neg_bitmap[BRANCH_BITMAP_SIZE] = {0};
static uint8_t context_bitmap[BRANCH_BITMAP_SIZE] = {0};
#endif

#if 0
static uint8_t memory_bitmap[BRANCH_BITMAP_SIZE] = {0};
#endif

static uintptr_t last_branch_hash = 0;
static int last_branch_is_interesting = 0;

#define IS_POWER_OF_TWO(x) ((x & (x - 1)) == 0)

#if CONTEXT_SENSITIVITY
static GHashTable* visited_branches = NULL;
#endif

// same as QSYM
static inline uintptr_t hash_pc(uintptr_t pc, uint8_t taken)
{
    if (taken) {
        taken = 1;
    }

    XXH32_state_t state;
    XXH32_reset(&state, 0); // seed = 0
    XXH32_update(&state, &pc, sizeof(pc));
    XXH32_update(&state, &taken, sizeof(taken));
    return XXH32_digest(&state) % BRANCH_BITMAP_SIZE;
}

static inline void load_bitmap(const char* path, uint8_t* data, size_t size)
{
    FILE* fp = fopen(path, "r");
    if (!fp) {
        printf("[SOLVER] Bitmap %s does not exist. Initializing it (%lu).\n", path, size);
        memset(data, 0, size);
        return;
    }
    int r = fread(data, 1, size, fp);
    if (r != size) {
        printf("[SOLVER] Invalid bitmap %s. Resetting it.\n", path);
        memset(data, 0, size);
    }
    fclose(fp);
}

void load_bitmaps()
{
    load_bitmap(config.branch_bitmap_path, branch_bitmap, BRANCH_BITMAP_SIZE);
#if BRANCH_COVERAGE == QSYM
    load_bitmap(config.context_bitmap_path, context_bitmap, BRANCH_BITMAP_SIZE);
#endif
#if 0
    load_bitmap(config.memory_bitmap_path, memory_bitmap, BRANCH_BITMAP_SIZE);
#endif
}

static inline void save_bitmap(const char* path, uint8_t* data, size_t size)
{
    FILE* fp = fopen(path, "w");
    int   r  = fwrite(data, 1, size, fp);
    if (r != size) {
        printf("[SOLVER] Failed to save bitmap: %s\n", path);
    }
    fclose(fp);
}

void save_bitmaps()
{
    save_bitmap(config.branch_bitmap_path, branch_bitmap, BRANCH_BITMAP_SIZE);
#if BRANCH_COVERAGE == QSYM
    save_bitmap(config.context_bitmap_path, context_bitmap, BRANCH_BITMAP_SIZE);
#endif
#if 0
    save_bitmap(config.memory_bitmap_path, memory_bitmap, BRANCH_BITMAP_SIZE);
#endif
}

// same as QSYM
static inline uintptr_t get_index(uintptr_t h)
{
    return ((last_branch_hash >> 1) ^ h) % BRANCH_BITMAP_SIZE;
}

#if BRANCH_COVERAGE == QSYM

#if CONTEXT_SENSITIVITY
// same as QSYM
static inline int is_interesting_context(uintptr_t h, uint8_t bits)
{
    // only care power of two
    if (!IS_POWER_OF_TWO(bits)) {
        return 0;
    }

    uint8_t interesting = 0;

    if (visited_branches == NULL) {
        visited_branches = g_hash_table_new(NULL, NULL);
    }

    gpointer       key, value;
    GHashTableIter iter;
    g_hash_table_iter_init(&iter, visited_branches);
    while (g_hash_table_iter_next(&iter, &key, &value)) {

        uintptr_t prev_h = (uintptr_t)key;

        // Calculate hash(prev_h || h)
        XXH32_state_t state;
        XXH32_reset(&state, 0);
        XXH32_update(&state, &prev_h, sizeof(prev_h));
        XXH32_update(&state, &h, sizeof(h));

        uintptr_t hash = XXH32_digest(&state) % (BRANCH_BITMAP_SIZE * CHAR_BIT);
        uintptr_t idx  = hash / CHAR_BIT;
        uintptr_t mask = 1 << (hash % CHAR_BIT);

        if ((context_bitmap[idx] & mask) == 0) {
            context_bitmap[idx] |= mask;
            interesting = 1;
        }
    }

    if (bits == 0) {
        g_hash_table_add(visited_branches, (gpointer)h);
    }

    return interesting;
}
#endif

// same as QSYM
int is_interesting_branch(uintptr_t pc, uintptr_t taken)
{
    uintptr_t h   = hash_pc(pc, taken);
    uintptr_t idx = get_index(h);
    uint8_t   ret = 1;

#if CONTEXT_SENSITIVITY
    uint8_t new_context = is_interesting_context(h, branch_neg_bitmap[idx]);
#endif

    branch_neg_bitmap[idx]++;

    if ((branch_neg_bitmap[idx] | branch_bitmap[idx]) != branch_bitmap[idx]) {

        uintptr_t inv_h   = hash_pc(pc, !taken);
        uintptr_t inv_idx = get_index(inv_h);

        branch_bitmap[idx] |= branch_neg_bitmap[idx];

        // mark the inverse case, because it's already covered by current
        // testcase
        branch_neg_bitmap[inv_idx]++;

        branch_bitmap[inv_idx] |= branch_neg_bitmap[inv_idx];
        // save_bitmaps();

        branch_neg_bitmap[inv_idx]--;
        ret = 1;
#if CONTEXT_SENSITIVITY
    } else if (new_context) {
        ret = 1;
        // save_bitmaps();
#endif
    } else {
        ret = 0;
    }

    last_branch_hash = h;
    last_branch_is_interesting = ret;
    return ret;
}

#elif BRANCH_COVERAGE == AFL
int is_interesting_branch(uintptr_t prev_loc, uintptr_t cur_loc)
{
    // printf("Prev: %lx - Curr: %lx\n", prev_loc, cur_loc);
    if (prev_loc > 0x600000 || cur_loc > 0x600000) {
        return 0;
    }

    prev_loc = (prev_loc >> 4) ^ (prev_loc << 8);
    prev_loc &= BRANCH_BITMAP_SIZE - 1;

    cur_loc = (cur_loc >> 4) ^ (cur_loc << 8);
    cur_loc &= BRANCH_BITMAP_SIZE - 1;

    uintptr_t idx = cur_loc ^ prev_loc;
    if (branch_bitmap[idx] == 0) {
        branch_bitmap[idx]++;
        last_branch_is_interesting = 1;
        return 1;
    }

    last_branch_is_interesting = 0;
    return 0;
}

#elif BRANCH_COVERAGE == FUZZOLIC
int is_interesting_branch(uintptr_t idx, uintptr_t run_bitmap_idx)
{
    //printf("global[%lu]=%u vs local[%lu]=%lu\n", idx, branch_bitmap[idx], idx, run_bitmap_idx + 1);
    if (run_bitmap_idx < 255 && run_bitmap_idx + 1 > branch_bitmap[idx]) {

        branch_bitmap[idx] = run_bitmap_idx + 1;

        last_branch_is_interesting = 1;
        return 1;
    }

    last_branch_is_interesting = 0;
    return 0;
}
#endif

int is_interesting_memory(uintptr_t addr)
{
    return last_branch_is_interesting;
#if 0
    uintptr_t h   = hash_pc(addr, 0);
    uintptr_t idx = get_index(h);
    uint8_t   ret = 0;

    if (memory_bitmap[idx] == 0) {
        memory_bitmap[idx] = 1;
        ret                = 1;
    }

    return ret;
#endif
}
