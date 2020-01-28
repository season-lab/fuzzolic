#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>

int simple_if(uint32_t);
int mystrcmp(const char* s1);
int all_concrete(uint32_t input);

// all flags add
int addq(uint64_t);
int addl(uint32_t);
int addw(uint16_t);
int addb(uint8_t);

// adc carry flag
int adcq(uint64_t);
int adcl(uint32_t);
int adcw(uint16_t);
int adcb(uint8_t);

typedef enum TestcaseInputMode {
    FIXED_SIZE,
    VARIABLE_SIZE,
} TestcaseInputMode;

typedef enum TestcaseInputType {
    VAR,
    BUFFER,
} TestcaseInputType;

typedef struct Testcase {
    const char* name;
    int (*f)(uintptr_t);
    TestcaseInputType input_type;
    TestcaseInputMode input_mode;
    size_t            input_size;
} Testcase;

#define F(x) ((int (*)(uintptr_t))x)

#define MAX_INPUT_SIZE 256
uint8_t data[MAX_INPUT_SIZE] = {0};

Testcase tests[] = {
    {.name       = "simple_if",
     .f          = F(simple_if),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 4},
    {.name       = "mystrcmp",
     .f          = F(mystrcmp),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "all_concrete",
     .f          = F(all_concrete),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 4},
    //
    {.name       = "addq",
     .f          = F(addq),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "addl",
     .f          = F(addl),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "addw",
     .f          = F(addw),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "addb",
     .f          = F(addb),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    //
    {.name       = "adcq",
     .f          = F(adcq),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "adcl",
     .f          = F(adcl),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "adcw",
     .f          = F(adcw),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "adcb",
     .f          = F(adcb),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
};

void foo(Testcase* t)
{
    read(0, data, t->input_size);
    int r;
    if (t->input_type == VAR) {
        switch (t->input_size) {
            case 8:;
                uint64_t q = *((uint64_t*)data);
                r          = t->f(q);
                break;
            case 4:;
                uint32_t l = *((uint32_t*)data);
                r          = t->f(l);
                break;
            case 2:;
                uint32_t w = *((uint16_t*)data);
                r          = t->f(w);
                break;
            case 1:;
                uint32_t b = *((uint8_t*)data);
                r          = t->f(b);
                break;
            default:
                assert("input size not supported");
        }

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
            //printf("Input bytes at %p\n", data);
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