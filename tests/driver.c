#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>

int simple_if(uint32_t);
int nested_if(uint32_t input);
int mystrcmp(const char* s1);
int all_concrete(uint32_t input);
int div3(int32_t input);

// jump table
int switchf(int v);

// symbolic load loop
int atoi_check(const char* s);

// slice
int symbolic_index(unsigned char index);
int symbolic_read(unsigned char* buffer);

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

// models
int model_strcmp(const char* s1);
int model_strncmp(const char* s1);
int model_strlen(const char* s1);
int model_strnlen_v0(const char* s1);
int model_strnlen_v1(const char* s1);
int model_memcmp_v0(const char* s1);
int model_memcmp_v1(const char* s1);
int model_memchr(const char* s1);
int model_malloc_min(uint32_t);
int model_malloc_max(uint32_t);
int model_realloc_min(uint32_t);
int model_realloc_max(uint32_t);

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

#define MAX_INPUT_SIZE 512
uint8_t data[MAX_INPUT_SIZE] = {0};

Testcase tests[] = {
    {.name       = "simple_if",
     .f          = F(simple_if),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 4},
    {.name       = "nested_if",
     .f          = F(nested_if),
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
    {.name       = "div3",
     .f          = F(div3),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 4},
    //
    {.name       = "switch",
     .f          = F(switchf),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 4},
    //
    {.name       = "atoi",
     .f          = F(atoi_check),
     .input_type = BUFFER,
     .input_size = 128},
    //
    {.name       = "symbolic_index",
     .f          = F(symbolic_index),
     .input_mode = FIXED_SIZE,
     .input_size = 1},
    //
    {.name       = "symbolic_read",
     .f          = F(symbolic_read),
     .input_type = BUFFER,
     .input_size = 256},
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
    //
    {.name       = "model_strcmp",
     .f          = F(model_strcmp),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "model_strncmp",
     .f          = F(model_strncmp),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "model_strlen",
     .f          = F(model_strlen),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "model_strnlen_v0",
     .f          = F(model_strnlen_v0),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "model_strnlen_v1",
     .f          = F(model_strnlen_v1),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "model_memcmp_v0",
     .f          = F(model_memcmp_v1),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "model_memcmp_v1",
     .f          = F(model_memcmp_v1),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "model_memchr",
     .f          = F(model_memchr),
     .input_type = BUFFER,
     .input_size = 128},
    {.name       = "model_malloc_min",
     .f          = F(model_malloc_min),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "model_malloc_max",
     .f          = F(model_malloc_max),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "model_realloc_min",
     .f          = F(model_realloc_min),
     .input_type = VAR,
     .input_mode = FIXED_SIZE,
     .input_size = 8},
    {.name       = "model_realloc_max",
     .f          = F(model_realloc_max),
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