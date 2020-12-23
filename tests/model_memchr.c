#include <unistd.h>
#include <stdio.h>
#include <string.h>

int model_memchr(const char* s1)
{
    if (memchr(s1, 'F', 8) != NULL)
        return 1;
    else
        return 0;
}
