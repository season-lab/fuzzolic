#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

#include "solver.h"

void parse_opts(int argc, char* argv[], Config* config)
{
    assert(config);
    int error = 0;
    int opt;
    while ((opt = getopt(argc, argv, ":i:t:o:b:c:m:sap")) != -1) {
        switch (opt) {
            case 'i':
                config->testcase_path = optarg;
                break;
            case 't':
                config->testcase_dir = optarg;
                break;
            case 'o':
                config->output_dir = optarg;
                break;
            case 'b':
                config->branch_bitmap_path = optarg;
                break;
            case 'c':
                config->context_bitmap_path = optarg;
                break;
            case 'm':
                config->memory_bitmap_path = optarg;
                break;
            case 'p':
                config->optimistic_solving = 1;
                break;
            case 's':
                config->memory_slice_reasoning = 1;
                break;
            case 'a':
                config->address_reasoning = 1;
                break;
            case ':':
                printf("Option %c needs a value\n", optopt);
                error = 1;
                break;
            case '?':
                printf("Unknown option: %c\n", optopt);
                error = 1;
                break;
        }
    }

    if (error || !(config->testcase_path) || !(config->testcase_dir) ||
        !(config->output_dir) || !(config->branch_bitmap_path) ||
        !(config->context_bitmap_path) || !(config->memory_bitmap_path)) {
        printf("Usage: %s [-a] [-p] [-s] -i <current_testcase> -t <testcase_dir> -o "
               "-b <branch_bitmap> -c <context_bitmap> -m memory_bitmap -o <output_dir>\n\n"
               "Optional arguments:\n"
               "  -s       - enable memory slice reasoning\n"
               "  -a       - enable address reasoning\n"
               "  -p       - enable optimistic solving\n",
               argv[0]);
        exit(1);
    }

    char * var = getenv("EXPR_POOL_SHM_KEY");
    printf("%s\n", var);
    if (var) {
        config->expr_pool_shm_key = (uintptr_t)strtoull(var, NULL, 16);
        assert(config->expr_pool_shm_key != ULLONG_MAX);
    }
    assert(config->expr_pool_shm_key != 0 && "Missing EXPR_POOL_SHM_KEY");

    var = getenv("QUERY_SHM_KEY");
    if (var) {
        config->query_shm_key = (uintptr_t)strtoull(var, NULL, 16);
        assert(config->query_shm_key != ULLONG_MAX);
    }
    assert(config->query_shm_key != 0 && "Missing QUERY_SHM_KEY");

#if BRANCH_COVERAGE == FUZZOLIC
    var = getenv("BITMAP_SHM_KEY");
    if (var) {
        config->bitmap_shm_key = (uintptr_t)strtoull(var, NULL, 16);
        assert(s_config->bitmap_shm_key != ULLONG_MAX);
    }
    assert(config->bitmap_shm_key != 0 && "Missing BITMAP_SHM_KEY");
#endif

    var = getenv("SOLVER_TIMEOUT");
    if (var) {
        config->timeout = (uintptr_t)strtoull(var, NULL, 10);
        assert(config->timeout != ULLONG_MAX);
    }
}
