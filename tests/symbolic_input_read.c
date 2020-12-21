#include <stdio.h>

int symbolic_read(unsigned char* buffer)
{
    unsigned short a = ((unsigned short*)buffer)[0];
    if (a >= 256)
        return 2;
    if (a == ((unsigned short*)buffer)[a])
        return 1;
    else
        return 0;
}