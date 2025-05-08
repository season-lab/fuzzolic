#include <stdlib.h>

int atoi_check(const char* s)
{
    if (atoi(s) == 1234)
        return 1;
    else
        return 0;
}