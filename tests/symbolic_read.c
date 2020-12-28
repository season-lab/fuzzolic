#include <stdio.h>

int symbolic_read(unsigned char* buffer)
{
    unsigned short a = ((unsigned short*)buffer)[0];
    // printf("Index value is %d\n", a);
    if (a >= 256)
        return 2;
    // printf("Value at index %d\n", ((unsigned short*)buffer)[a]);
    if (a == ((unsigned short*)buffer)[a])
        return 1;
    else
        return 0;
}