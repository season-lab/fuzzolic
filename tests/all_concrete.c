#include <stdint.h>

#define N 512
int all_concrete(uint32_t input) {

    int sum = 0;
    int i, j, k;
    for (i = 0; i < N; i++)
        for (j = 0; j < N; j++)
            for (k = 0; k < N; k++)
                sum++;

    char * data = (char *) &input;
    if (data[0] == 'D')
        if (data[1] == 'E')
            if (data[2] == 'A')
                if (data[3] == 'D')
                    return 1;

    return 0;
}
