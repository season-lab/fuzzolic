#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>

int simple_if(uint32_t);

int addq(uint64_t);
int addl(uint32_t);

// adc carry flag
int adcq(uint64_t);
int adcl(uint32_t);
int adcw(uint16_t);
int adcb(uint8_t);

typedef enum TestcaseInputType {
    VAR,
    BUFFER,
} TestcaseInputType;

typedef struct Testcase {
    const char* name;
    int (*f)(uintptr_t);
    TestcaseInputType input_type;
    size_t            input_size;
} Testcase;

#define F(x) ((int (*)(uintptr_t))x)

#define MAX_INPUT_SIZE 256
uint8_t data[MAX_INPUT_SIZE] = {0};

Testcase tests[] = {
    {.name       = "simple_if",
     .f          = F(simple_if),
     .input_type = VAR,
     .input_size = 8},
    //
    {.name = "addq", .f = F(addq), .input_type = VAR, .input_size = 8},
    {.name = "addl", .f = F(addl), .input_type = VAR, .input_size = 8},
    //
    {.name = "adcq", .f = F(adcq), .input_type = VAR, .input_size = 8},
    {.name = "adcl", .f = F(adcl), .input_type = VAR, .input_size = 8},
    {.name = "adcw", .f = F(adcw), .input_type = VAR, .input_size = 8},
    {.name = "adcb", .f = F(adcb), .input_type = VAR, .input_size = 8},
};

void foo(Testcase* t)
{
    read(0, data, sizeof(t->input_size));
    int r;
    if (t->input_type == VAR) {
        uint64_t p = *((uint64_t*)data);
        r          = t->f(p);
    } else {
        r = t->f((uint64_t)data);
    }
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
            assert(tests[i].input_size < MAX_INPUT_SIZE);
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