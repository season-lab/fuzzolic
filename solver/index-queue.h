#ifndef INDEX_QUEUE_H
#define INDEX_QUEUE_H

#include <string.h>

#define HAS_VALUE 1
#define HAS_INDEX 2
#define HAS_INDEX_AND_VALUE 3

#define ADD_VALUE_ALWAYS

#define INDEX_QUEUE_SIZE 10
#define VALUE_QUEUE_SIZE 10
#define MAX_GROUP_SIZE 8
#define CLEAR_INDEX_VALUE_QUEUE()                                              \
    do {                                                                       \
        memset((void*)&index_queue, 0, sizeof(index_group_t));                 \
        index_queue.size_max = INDEX_QUEUE_SIZE;                               \
        memset((void*)&value_queue, 0, sizeof(value_queue_t));                 \
        value_queue.size_max = VALUE_QUEUE_SIZE;                               \
    } while (0)

#define ADD_VALUE(v)                                                           \
    do {                                                                       \
        if (value_queue.size < value_queue.size_max) {                         \
            value_queue.values[value_queue.size++] = v;                        \
        }                                                                      \
    } while (0)

#define ADD_INDEX(i, group)                                                    \
    do {                                                                       \
        if (index_queue.index_groups[group].n < MAX_GROUP_SIZE) {              \
            unsigned char idx = index_queue.index_groups[group].n++;           \
            index_queue.index_groups[group].indexes[idx] = i;                  \
        }                                                                      \
    } while (0)

typedef struct index_group_t {
    unsigned char n;                       // number of valid indexes
    unsigned long indexes[MAX_GROUP_SIZE]; // indexes
} index_group_t;

typedef struct index_queue_t {
    unsigned int  size;     // index of next free index group
    unsigned int  size_max; // size of queue
    index_group_t index_groups[INDEX_QUEUE_SIZE]; // index groups
} index_queue_t;

typedef struct value_queue_t {
    unsigned int  size;
    unsigned int  size_max;
    unsigned long values[VALUE_QUEUE_SIZE];
} value_queue_t;

index_queue_t index_queue = {.size = 0, .size_max = INDEX_QUEUE_SIZE};
value_queue_t value_queue = {.size = 0, .size_max = VALUE_QUEUE_SIZE};

static inline void print_index_and_value_queue()
{
    SAYF("----- QUEUE -----\n");
    int i, j;
    for (i = 0; i < value_queue.size; ++i)
        SAYF("value: 0x%lx\n", value_queue.values[i]);
    for (i = 0; i < index_queue.size; ++i)
        for (j = 0; j < index_queue.index_groups[i].n; ++j)
            SAYF("group: %d. index: 0x%lx\n", i,
                 index_queue.index_groups[i].indexes[j]);
    SAYF("-----------------\n");
}

#endif