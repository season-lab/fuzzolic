#include <stdint.h>

int nested_if(uint32_t input) {

    char * data = (char *) &input;
    if (data[0] == 'D')
        if (data[1] == 'E')
            if (data[2] == 'A')
                if (data[3] == 'D')
                    return 1;

    return 0;
}
