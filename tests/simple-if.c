char DATA[128];

int foo(int p){
    if (p == 0xDEADBEEF)
        printf("Got me!\n");
    else
        printf("Got you!\n");
}

int main() {
    int a = 10;
    a = a + 20;
    DATA[20] = a;
    char * m = malloc(0xABC);
    m[10] = a;
    foo(0);
    return 0;
}