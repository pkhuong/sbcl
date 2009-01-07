#ifndef _HASH_TABLE_H_

#define _HASH_TABLE_H_

#if N_WORD_BITS == 64
# define HASH_TABLE_SIZE (1UL << 16)
#else
# define HASH_TABLE_SIZE (1UL << 12)
#endif

typedef unsigned long size_t;

typedef struct page_descriptor {
        /* if there's only 1 entry */
        size_t middle;
        table_value_t value;
        /* if not NULL, all in vector */
        table_value_t * values;
} page_descriptor_t;

typedef struct bucket {
        size_t descriptor_top;
        page_descriptor_t descriptor;
        size_t ndescriptors;
        size_t max_descriptors;
        size_t * tops;
        page_descriptor_t * descriptors;
} bucket_t;

typedef struct table {
        bucket_t buckets[HASH_TABLE_SIZE];
} table_t;

void init_table (table_t *);
table_t * make_table();

table_value_t * hash_table_get (table_t *, size_t);
table_value_t hash_table_set (table_t *, size_t key, table_value_t value);
table_value_t hash_table_del (table_t *, size_t);
#endif
