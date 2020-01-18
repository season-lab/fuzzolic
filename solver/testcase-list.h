#ifndef TESTCASE_LIST_H
#define TESTCASE_LIST_H

#include <z3.h>

#define MAX_TESTCASE_LIST_SIZE 100

typedef struct testcase_t {
    unsigned char* testcase;
    Z3_ast         z3_formula;
    unsigned long  len;
} testcase_t;

typedef struct testcase_list_t {
    testcase_t    list[MAX_TESTCASE_LIST_SIZE];
    unsigned long size;
    unsigned long max_size;
} testcase_list_t;

void init_testcase_list(testcase_list_t* t);
void free_testcase_list(testcase_list_t* t);
void load_testcase_folder(testcase_list_t* t, char* testcase_dir,
                          Z3_context ctx);
void load_testcase(testcase_list_t* t, char const* filename, Z3_context ctx);

extern testcase_list_t testcase_list;

#endif