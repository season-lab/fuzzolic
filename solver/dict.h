#ifndef DICT_H
#define DICT_H

#include <strings.h>
#include <assert.h>

#endif

#ifndef DICT_N_BUCKETS
#define DICT_N_BUCKETS 1024
#endif

#ifndef glue
#define xglue(x, y) x##y
#define glue(x, y) xglue(x, y)
#endif

#ifndef DICT_DATA_T
#define DICT_DATA_T long
#endif

typedef struct glue(dict_el__, DICT_DATA_T)
{
    unsigned long key;
    DICT_DATA_T   el;
}
glue(dict_el_, DICT_DATA_T);

#define DICT_EL glue(dict_el_, DICT_DATA_T)
#define DA_DATA_T DICT_EL
#define DA_INIT_SIZE 5
#include "dynamic-array.h"

typedef struct glue(dict__, DICT_DATA_T)
{
    glue(da__, DICT_EL) * buckets;
    unsigned long  size;
    unsigned long* filled_buckets;
    unsigned long  filled_buckets_i;
}
glue(dict__, DICT_DATA_T);

static inline void glue(dict_init__,
                        DICT_DATA_T)(glue(dict__, DICT_DATA_T) * dict)
{
    dict->filled_buckets_i = 0;
    dict->size             = 0;
    dict->buckets = (glue(da__, DICT_EL)*)malloc(sizeof(glue(da__, DICT_EL)) *
                                                 DICT_N_BUCKETS);
    assert(dict->buckets != 0 && "dict dict_init() - malloc failed");
    dict->filled_buckets =
        (unsigned long*)malloc(sizeof(unsigned long) * DICT_N_BUCKETS);
    assert(dict->filled_buckets != 0 && "dict dict_init() - malloc failed");

    // this memset is crucial
    memset(dict->buckets, 0, sizeof(glue(da__, DICT_EL)) * DICT_N_BUCKETS);
}

static inline void glue(dict_set__,
                        DICT_DATA_T)(glue(dict__, DICT_DATA_T) * dict,
                                     unsigned long key, DICT_DATA_T el)
{
    unsigned long bucket_id = key % DICT_N_BUCKETS;

    DICT_EL dict_el;
    glue(da__, DICT_EL)* bucket = &dict->buckets[bucket_id];

    if (bucket->data == 0) {
        // uninitialized bucket
        dict->filled_buckets[dict->filled_buckets_i++] = bucket_id;
        glue(da_init__, DICT_EL)(bucket);

        dict_el.el  = el;
        dict_el.key = key;
        dict->size++;
        glue(da_add_item__, DICT_EL)(bucket, dict_el);
    } else if (bucket->size == 0) {
        // initialized but empty (as a consequence of set_remove_all)
        dict->filled_buckets[dict->filled_buckets_i++] = bucket_id;

        dict_el.el  = el;
        dict_el.key = key;
        dict->size++;
        glue(da_add_item__, DICT_EL)(bucket, dict_el);
    } else {
        // collision
        unsigned i, is_present = 0;
        for (i = 0; i < bucket->size; ++i) {
            DICT_EL* tmp = glue(da_get_ref_item__, DICT_EL)(bucket, i);
            if (tmp->key == key) {
                tmp->el    = el;
                is_present = 1;
                break;
            }
        }
        if (!is_present) {
            dict_el.el  = el;
            dict_el.key = key;
            dict->size++;
            glue(da_add_item__, DICT_EL)(bucket, dict_el);
        }
    }
}

static inline DICT_DATA_T* glue(dict_get_ref__,
                                DICT_DATA_T)(glue(dict__, DICT_DATA_T) * dict,
                                             unsigned long key)
{
    unsigned long bucket_id = key % DICT_N_BUCKETS;

    glue(da__, DICT_EL)* bucket = &dict->buckets[bucket_id];

    if (bucket->data == 0) {
        return 0;
    }
    unsigned i;
    for (i = 0; i < bucket->size; ++i) {
        DICT_EL* tmp = glue(da_get_ref_item__, DICT_EL)(bucket, i);
        if (tmp->key == key) {
            return &tmp->el;
        }
    }
    return 0;
}

#ifndef DICT_NO_GET
static inline DICT_DATA_T glue(dict_get__,
                                DICT_DATA_T)(glue(dict__, DICT_DATA_T) * dict,
                                             unsigned long key)
{
    unsigned long bucket_id = key % DICT_N_BUCKETS;

    glue(da__, DICT_EL)* bucket = &dict->buckets[bucket_id];

    if (bucket->data == 0) {
        return  (DICT_DATA_T) 0;
    }
    unsigned i;
    for (i = 0; i < bucket->size; ++i) {
        DICT_EL* tmp = glue(da_get_ref_item__, DICT_EL)(bucket, i);
        if (tmp->key == key) {
            return tmp->el;
        }
    }
    return (DICT_DATA_T) 0;
}
#endif

static inline int glue(dict_contains__,
                                DICT_DATA_T)(glue(dict__, DICT_DATA_T) * dict,
                                             unsigned long key, DICT_DATA_T* value)
{
    unsigned long bucket_id = key % DICT_N_BUCKETS;

    glue(da__, DICT_EL)* bucket = &dict->buckets[bucket_id];

    if (bucket->data == 0) {
        return 0;
    }
    unsigned i;
    for (i = 0; i < bucket->size; ++i) {
        DICT_EL* tmp = glue(da_get_ref_item__, DICT_EL)(bucket, i);
        if (tmp->key == key) {
            if (value) {
                *value = tmp->el;
            }
            return 1;
        }
    }
    return 0;
}

static inline void glue(dict_remove_all__,
                        DICT_DATA_T)(glue(dict__, DICT_DATA_T) * dict,
                                     void (*free_el)(DICT_DATA_T*))
{
    unsigned long i;
    for (i = 0; i < dict->filled_buckets_i; ++i) {
        glue(da__, DICT_EL)* bucket = &dict->buckets[dict->filled_buckets[i]];
        if (free_el != 0) {
            unsigned long j;
            for (j = 0; j < bucket->size; ++j)
                free_el(&bucket->data[j].el);
        }
        glue(da_remove_all__, DICT_EL)(bucket);
    }

    dict->filled_buckets_i = 0;
}

static inline void glue(dict_free__,
                        DICT_DATA_T)(glue(dict__, DICT_DATA_T) * dict,
                                     void (*free_el)(DICT_DATA_T*))
{
    unsigned long i;
    for (i = 0; i < DICT_N_BUCKETS; ++i) {
        glue(da__, DICT_EL)* bucket = &dict->buckets[i];
        if (bucket->data == 0)
            continue;
        if (free_el != 0) {
            unsigned long j;
            for (j = 0; j < bucket->size; ++j)
                free_el(&bucket->data[j].el);
        }
        glue(da_free__, DICT_EL)(bucket, 0);
    }
    free(dict->buckets);
    free(dict->filled_buckets);
    dict->buckets        = 0;
    dict->filled_buckets = 0;
}

#undef DICT_DATA_T
#undef DICT_N_BUCKETS
