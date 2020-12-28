#include <stdio.h>
#include <stdlib.h>

int magic_check(int p){
    if (p == 0xDEADBEEF)
        return 1;
    else
        return 0;
}

int get_input(char* fname) {
    FILE* fp = fopen(fname, "r");
    if (fp == NULL) exit(EXIT_FAILURE);
    int data;
    int r = fread(&data, 1, sizeof(data), fp);
    if (r != sizeof(data)) exit(EXIT_FAILURE);
    fclose(fp);
    return data;
}

int main(int argc, char* argv[]) {

    if (argc != 2) exit(EXIT_FAILURE);
    int input = get_input(argv[1]); // read four bytes from the input file
    if (magic_check(input)) {
        printf("Correct value [%x] :)\n", input);
    } else {
        printf("Wrong value [%x] :(\n", input);
    }

    return 0;
}