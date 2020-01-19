#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

int adcq(uint64_t);
int adcl(uint32_t);
int adcw(uint16_t);
int adcb(uint8_t);

typedef struct Testcase {
    const char* name;
    int (*f)(uintptr_t);
} Testcase;

Testcase tests[] = {
    {.name = "adcq", .f = adcq},
    {.name = "adcl", .f = (int (*)(uintptr_t))adcl},
    {.name = "adcw", .f = (int (*)(uintptr_t))adcw},
    {.name = "adcb", .f = (int (*)(uintptr_t))adcb},
};

void foo(Testcase* t)
{
    uint64_t p;
    read(0, &p, sizeof(p));
    int r = t->f(p);
    printf("RESULT=%d\n", r);
}

int main(int argc, char* argv[])
{
    if (argc != 2) {
        printf("%s {adcq, adcl}\n", argv[0]);
        exit(1);
    }

    const char* testcase_name = argv[1];

    size_t i;
    for (i = 0; i < sizeof(tests) / sizeof(Testcase); i++) {
        if (strcmp(testcase_name, tests[i].name) == 0) {
            foo(&tests[i]);
            break;
        }
    }

    return 0;
}