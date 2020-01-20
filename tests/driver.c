#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

int simple_if(uint32_t);

int addq(uint64_t);
int addl(uint32_t);

// adc carry flag
int adcq(uint64_t);
int adcl(uint32_t);
int adcw(uint16_t);
int adcb(uint8_t);

typedef struct Testcase {
    const char* name;
    int (*f)(uintptr_t);
} Testcase;

#define F(x) ((int (*)(uintptr_t))x)

Testcase tests[] = {
    {.name = "simple_if", .f = F(simple_if)},
    //
    {.name = "addq", .f = F(addq)},
    {.name = "addl", .f = F(addl)},
    //
    {.name = "adcq", .f = F(adcq)},
    {.name = "adcl", .f = F(adcl)},
    {.name = "adcw", .f = F(adcw)},
    {.name = "adcb", .f = F(adcb)},
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
        printf("%s {", argv[0]);
        size_t i;
        for (i = 0; i < sizeof(tests) / sizeof(Testcase); i++) {
            printf("%s, ", tests[i].name);
        }
        printf("}\n");
        exit(1);
    }

    const char* testcase_name = argv[1];

    size_t i, found = 0;
    for (i = 0; i < sizeof(tests) / sizeof(Testcase); i++) {
        if (strcmp(testcase_name, tests[i].name) == 0) {
            foo(&tests[i]);
            found = 1;
            break;
        }
    }

    if (!found) {
        printf("Testcase %s not available\n", testcase_name);
        exit(1);
    }

    return 0;
}