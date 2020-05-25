static char data[256] = { 0 };

int symbolic_index(unsigned char index)
{
    data[65] = 23;
    if (data[index] == 23)
        return 1;
    else
        return 0;
}