#ifndef DYNAMIC_ARRAY_H
#define DYNAMIC_ARRAY_H

#include <stdlib.h>
#include <assert.h>
#include <string.h>

#endif

#ifndef glue
#define xglue(x, y) x##y
#define glue(x, y) xglue(x, y)
#endif

#ifndef DA_INIT_SIZE
#define DA_INIT_SIZE 100
#endif

#ifndef DA_DATA_T
#define DA_DATA_T long
#endif

typedef struct glue(da__, DA_DATA_T)
{
    DA_DATA_T*    data;
    unsigned long max_size;
    unsigned long size;
}
glue(da__, DA_DATA_T);

static inline void glue(da_init__, DA_DATA_T)(glue(da__, DA_DATA_T) * da)
{
    da->data = (DA_DATA_T*)malloc(DA_INIT_SIZE * sizeof(DA_DATA_T));
    assert(da->data != 0 && "dynamic-array da_init() - malloc failed");
    da->max_size = DA_INIT_SIZE;
    da->size     = 0;
}

static inline void glue(da_free__, DA_DATA_T)(glue(da__, DA_DATA_T) * da,
                                              void (*el_free)(DA_DATA_T*))
{
    if (el_free != NULL) {
        unsigned long i;
        for (i = 0; i < da->size; ++i)
            el_free(&da->data[i]);
    }
    free(da->data);
    da->data     = NULL;
    da->max_size = 0;
    da->size     = 0;
}

static inline void glue(da_remove_all__, DA_DATA_T)(glue(da__, DA_DATA_T) * da)
{
    // memset((void*)da->data, 0, da->size * sizeof(DA_DATA_T));
    da->data =
        da->max_size > DA_INIT_SIZE
            ? (DA_DATA_T*)realloc(da->data, DA_INIT_SIZE * sizeof(DA_DATA_T))
            : da->data;
    assert(da->data != 0 && "dynamic-array da_remove_all() - realloc failed");
    da->max_size = DA_INIT_SIZE;
    da->size     = 0;
}

static inline void glue(da_add_item__, DA_DATA_T)(glue(da__, DA_DATA_T) * da,
                                                  DA_DATA_T el)
{
    if (da->size >= da->max_size) {
        da->max_size *= 2;
        da->data = (DA_DATA_T*)realloc((void*)da->data,
                                       da->max_size * sizeof(DA_DATA_T));
        assert(da->data != 0 && "dynamic-array da_add_item() - realloc failed");
    }
    da->data[da->size++] = el;
}

static inline DA_DATA_T glue(da_get_item__,
                             DA_DATA_T)(glue(da__, DA_DATA_T) * da,
                                        unsigned long idx)
{
    assert(idx < da->size && "dynamic-array get_item() - out of range");
    return da->data[idx];
}

static inline DA_DATA_T* glue(da_get_ref_item__,
                              DA_DATA_T)(glue(da__, DA_DATA_T) * da,
                                         unsigned long idx)
{
    assert(idx < da->size && "dynamic-array get_ref_item() - out of range");
    return &da->data[idx];
}

#undef DA_DATA_T
#undef DA_INIT_SIZE
