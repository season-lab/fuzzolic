#include <unistd.h>
#include <stdio.h>

int foo(void){
    char data[128];
    read(0, &data, sizeof(data));
    //printf("Input: %s\n", data);
    if (strcmp(data, "DEADBEEF") == 0)
        printf("Got me!\n");
    else
        printf("Got you!\n");
}

int main() {
    foo();
    return 0;
}
