#include <unistd.h>
#include <stdio.h>
#include <string.h>


int model_memcmp_v0(const char* s1)
{
    if (memcmp(s1, "DEADBEEF", 4) == 0)
        return 1;
    else
        return 0;
}

// we use a different input testcase
int model_memcmp_v1(const char* s1)
{
    if (memcmp(s1, "DEADBEEF", 4) == 0)
        return 1;
    else
        return 0;
}