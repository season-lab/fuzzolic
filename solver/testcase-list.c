#include <fts.h>
#include "testcase-list.h"
#include "debug.h"

// testcase list
testcase_list_t testcase_list = {0};

void init_testcase_list(testcase_list_t* t)
{
    t->max_size = MAX_TESTCASE_LIST_SIZE;
}

void free_testcase_list(testcase_list_t* t)
{
    int i;
    for (i = 0; i < t->size; ++i)
        free(t->list[i].testcase);
    t->size = 0;
}

void load_testcase(testcase_list_t* t, char const* filename, Z3_context ctx)
{
    if (t->size >= t->max_size)
        ABORT("testcase_list is full\n");

    testcase_t*   tc = &t->list[t->size++];
    FILE*         fp = fopen(filename, "r");
    int           res, i = 0;
    unsigned char c;

    if (fp == NULL)
        PFATAL("fopen() failed");

    fseek(fp, 0L, SEEK_END);
    tc->len = ftell(fp);
    fseek(fp, 0L, SEEK_SET);

    tc->testcase    = (unsigned char*)malloc(sizeof(unsigned char) * tc->len);
    tc->z3_formula  = NULL;
    Z3_sort bv_sort = Z3_mk_bv_sort(ctx, 8);

    while (1) {
        res = fread(&c, sizeof(char), 1, fp);
        if (res != 1)
            break;
        tc->testcase[i] = c;
        if (tc->z3_formula == NULL)
            tc->z3_formula = Z3_mk_unsigned_int(ctx, c, bv_sort);
        else
            tc->z3_formula = Z3_mk_concat(
                ctx, Z3_mk_unsigned_int(ctx, c, bv_sort), tc->z3_formula);
    }
}

void load_testcase_folder(testcase_list_t* t, char* testcase_dir,
                          Z3_context ctx)
{
    FTS*        ftsp;
    FTSENT *    p, *chp;
    int         fts_options = FTS_LOGICAL | FTS_NOCHDIR;
    char* const file_list[] = {testcase_dir, NULL};

    SAYF("Loading testcases from %s \n", testcase_dir);

    if ((ftsp = fts_open(file_list, fts_options, NULL)) == NULL)
        ABORT("error in fts_open. %s\n", testcase_dir);

    chp = fts_children(ftsp, 0);
    if (chp == NULL)
        ABORT("error in fts_children. %s\n", testcase_dir);

    while ((p = fts_read(ftsp)) != NULL) {
        switch (p->fts_info) {
            case FTS_D:
                SAYF("found directory\t %s skipping\n", p->fts_path);
                break;
            case FTS_F:
                SAYF("found testcase\t %s loading... ", p->fts_path);
                load_testcase(t, p->fts_path, ctx);
                SAYF("done!\n");
                break;
            default:
                break;
        }
    }
    fts_close(ftsp);
}
