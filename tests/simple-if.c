#include <unistd.h>
#include <stdio.h>

int foo(void){
    int p;
    read(0, &p, sizeof(p));
    //printf("Input: %x\n", p);
    if (p == 0xDEADBEEF)
        printf("Got me!\n");
    else
        printf("Got you!\n");
}

int main() {
    foo();
    return 0;
}
