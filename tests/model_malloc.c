#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

int model_malloc_min(int size)
{
    void* res = malloc(size);
    return size == 0;
}

int model_malloc_max(int size)
{
    void* res = malloc(size);
    return size > 128;
}

int model_realloc_min(int size)
{
    void* res = realloc(malloc(8), size);
    return size == 0;
}

int model_realloc_max(int size)
{
    void* res = realloc(malloc(8), size);
    return size > 128;
}