#include <stdio.h>
#include <stdlib.h>

#define BITMAP_SIZE 65536

char bitmap_src[BITMAP_SIZE] = { 0 };
char bitmap_dst[BITMAP_SIZE] = { 0 };

static void load_bitmap(char* path, char* bitmap)
{
    // printf("Loading bitmap: %s\n", path);
    FILE* fp = fopen(path, "r");
    if (!fp) {
        printf("Cannot open: %s\n", path);
        exit(1);
    }
    int count = 0;
    while (count < BITMAP_SIZE) {
        int res = fread(bitmap + count, 1, BITMAP_SIZE - count, fp);
        if (res <= 0) break;
        count += res;
    }
    if (count < BITMAP_SIZE) {
        printf("Cannot read full bitmap: %s [%d]\n", path, count);
        exit(1);
    }
    fclose(fp);
}

static void save_bitmap(char* path, char* bitmap)
{
    // printf("Saving bitmap: %s\n", path);
    FILE* fp = fopen(path, "w");
    if (!fp) {
        printf("Cannot open: %s\n", path);
        exit(1);
    }
    int count = 0;
    while (count < BITMAP_SIZE) {
        int res = fwrite(bitmap + count, 1, BITMAP_SIZE - count, fp);
        if (res <= 0) break;
        count += res;
    }
    if (count < BITMAP_SIZE) {
        printf("Cannot write full bitmap: %s [%d]\n", path, count);
        exit(1);
    }
    fclose(fp);
}

static int merge_bitmap(char* bitmap_src, char* bitmap_dst)
{
    int is_interesting = 0;
    for (int i = 0; i < BITMAP_SIZE; i++) {
        if ((bitmap_src[i] | bitmap_dst[i]) != bitmap_dst[i]) {
            is_interesting = 1;
            // printf("bitmap[%u] = %u\n", i, bitmap_dst[i]);
            bitmap_dst[i] |= bitmap_src[i];
            // printf("bitmap[%u] = %u\n", i, bitmap_dst[i]);
        }
    }
    return is_interesting;
}

int main(int argc, char* argv[])
{
    if (argc != 3) {
        printf("Usage: %s <bitmap_source> <bitmap_dest>\n", argv[0]);
        exit(1);
    }

    load_bitmap(argv[1], bitmap_src);
    load_bitmap(argv[2], bitmap_dst);
    int r = merge_bitmap(bitmap_src, bitmap_dst);
    if (r == 0) exit(2);
    save_bitmap(argv[2], bitmap_dst);

    return 0;
}