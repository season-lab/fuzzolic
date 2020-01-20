static int mystrcmp_internal(const char* s1, const char* s2)
{
    while (*s1 && (*s1 == *s2)) {
        s1++;
        s2++;
    }
    return *(const unsigned char*)s1 - *(const unsigned char*)s2;
}

int mystrcmp(const char* s1)
{
    if (mystrcmp_internal(s1, "DEADBEEF") == 0)
        return 1;
    else
        return 0;
}
