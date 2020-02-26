#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

#include "solver.h"

void parse_opts(int argc, char* argv[], Config* config)
{
    assert(config);
    int error = 0;
    int opt;
    while ((opt = getopt(argc, argv, ":i:t:o:b:c:")) != -1) {
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
        !(config->context_bitmap_path)) {
        printf("Usage: %s -i <current_testcase> -t <testcase_dir> -o "
               "-b <branch_bitmap> -c <context_bitmap> <output_dir>\n",
               argv[0]);
        exit(1);
    }
}