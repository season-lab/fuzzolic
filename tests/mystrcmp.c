#include <unistd.h>
#include <stdio.h>

int mystrcmp(const char* s1, const char* s2)
{
    while (*s1 && (*s1 == *s2)) {
        s1++;
        s2++;
    }
    return *(const unsigned char*)s1 - *(const unsigned char*)s2;
}

int foo(void)
{
    char data[128];
    read(0, &data, sizeof(data));
    // printf("Input: %s\n", data);
    if (mystrcmp(data, "DEADBEEF") == 0)
        printf("Got me!\n");
    else
        printf("Got you!\n");
}

int main()
{
    foo();
    return 0;
}
