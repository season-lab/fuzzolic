#include <unistd.h>
#include <stdio.h>

int model_strncmp(const char* s1)
{
    if (strncmp(s1, "DEADBEEF", 4) == 0)
        return 1;
    else
        return 0;
}
