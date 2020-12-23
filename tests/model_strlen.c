#include <unistd.h>
#include <stdio.h>
#include <string.h>

int model_strlen(const char* s1)
{
    if (strlen(s1) == 5)
        return 1;
    else
        return 0;
}

int model_strnlen_v0(const char* s1)
{
    if (strnlen(s1, 5) == 3)
        return 1;
    else
        return 0;
}

// we will use a different input test case
int model_strnlen_v1(const char* s1)
{
    if (strnlen(s1, 5) == 3)
        return 1;
    else
        return 0;
}