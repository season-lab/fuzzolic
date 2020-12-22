#include <unistd.h>
#include <stdio.h>

int model_strcmp(const char* s1)
{
    if (strcmp(s1, "DEADBEEF") == 0)
        return 1;
    else
        return 0;
}
