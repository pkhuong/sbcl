/*
Hash table for (medium/large -sized) objects.

Addresses are divided in three parts:

Top    bits: 20-63
Middle bits: 6-19
Bottom bits: 0-5 (0-4 on 32 bit)

Bottom bits are completely ignored, make sure address are aligned.

The top bits are used as keys in a hash table of page descriptors.

Once the correct descriptor has been found, the middle bit is used to
index in the descriptor.

The data structure has been specialised to minimize the number of
random accesses made in the common cases: < 1 descriptor per bucket
and 1 entry per descriptor.

The hash table is represented as an array of inline buckets.
Each bucket contains an inline descriptor (potentially empty), and
a pointer to an array of inline descriptors:

bucket: [[[top bits] [descriptor] [other top bits] [other descriptors]] ...]
                                    |                |
                                   /                  \
                                  v                    v
                         [[top bits] [top bits] ...] [[descriptors] ...]

If a bucket is empty, its [top bits] (actually, that of the inline
[descriptor]) are set to -1.

If a descriptor contains only one entry, it is saved inline, in the
[descriptor]: the [top bits] are set to the key, and the inline [descriptor]
filled:

descriptor: [[middle bits] [value] [NULL]]

If a descriptor contains more than one entry, they are saved in a dense
array, one location (value for [middle bits]) per possible entry:

descriptor: [[unused] [unused] [values]]
                                   |
                                   v
                                 [[value] [value] ...]

When a bucket contains more than one descriptor, all but the first
descriptors are stored in arrays. One array for the [top bits], and
one for the [descriptors].

Assuming all buckets all contain at most one page descriptor:

hash_table_get costs:
* 1 access to find the bucket's inline descriptor and look for a hit
* 0 access if there's only 1 entry in the descriptor
* 1 access if there are more than 1 entry in the descriptor

hash_table_set costs:
* 1 access to look in the bucket's inline descriptor for a hit
* 0 access if the descriptor is empty, or already contains the same key
* 1 access to index in the [values] array if there are more than 1 entry

  * A lot more (mostly a calloc) if a [values] array has to be created

 */

#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <stdio.h>

#ifdef _TEST_HASH_TABLE_
# include "cycle.h"

# ifndef N_WORD_BITS
#  define N_WORD_BITS 64
# endif

typedef size_t table_value_t;
#else
typedef void * table_value_t;
#endif

#include "hash-table.h"

#if N_WORD_BITS == 64
# define BOTTOM_BITS 6
# define LOW_BITS 20

static
size_t hash_address (size_t addr)
{
        addr >>= LOW_BITS;
        return addr;
//        return ((addr * 7919UL) >> 13) ^ addr;
}
#else
# define BOTTOM_BITS 5
# define LOW_BITS 20

static
size_t hash_address (size_t addr)
{
        return addr >> LOW_BITS;
}
#endif

#define MIDDLE_BITS (LOW_BITS - BOTTOM_BITS)

static table_value_t *
search_descriptor (page_descriptor_t * descriptor, size_t middle)
{
        if (descriptor->values)
                return &descriptor->values[middle];

        return (descriptor->middle == middle) ? &descriptor->value : NULL;
}

static void
init_descriptor (page_descriptor_t * descriptor,
                 size_t middle, table_value_t value)
{
        descriptor->middle = middle;
        descriptor->value = value;
        descriptor->values = NULL;
}

static table_value_t
descriptor_add (page_descriptor_t * descriptor,
                size_t middle, table_value_t value)
{
        if (descriptor->values) {
                table_value_t old = descriptor->values[middle];
                descriptor->values[middle] = value;
                return old;
        }

        if (descriptor->middle == middle) {
                table_value_t old = descriptor->value;
                descriptor->value = value;
                return old;
        }

        size_t first_middle = descriptor->middle;
        table_value_t first_value  = descriptor->value;

        descriptor->middle = -1UL;
        descriptor->value  = 0;

        table_value_t * values
                = descriptor->values
                = calloc((1UL << MIDDLE_BITS), sizeof(table_value_t));

        values[first_middle] = first_value;
        values[middle] = value;

        return 0;
}

static table_value_t
descriptor_del (page_descriptor_t * descriptor, size_t middle)
{
        if (descriptor->values) {
                table_value_t old = descriptor->values[middle];
                descriptor->values[middle] = 0;
                return old;
        }

        if (descriptor->middle == middle) {
                table_value_t old = descriptor->value;
                descriptor->middle = -1UL;
                descriptor->value = 0;
                return old;
        }

        return 0;
}

extern
void init_table (table_t * table)
{
        size_t i;
        bzero(table, sizeof(table_t));

        for (i = 0; i < HASH_TABLE_SIZE; i++)
                table->buckets[i].descriptor_top = -1UL;
}

extern
table_t * make_table ()
{
        table_t * table = malloc(sizeof(table_t));
        init_table(table);

        return table;
}

extern table_value_t *
hash_table_get (table_t * table, size_t addr)
{
        size_t hash = hash_address(addr) & (HASH_TABLE_SIZE-1);
        size_t top  = addr >> LOW_BITS;
        size_t middle = (addr >> BOTTOM_BITS) & ((1UL << MIDDLE_BITS)-1);

        bucket_t * bucket = table->buckets+hash;

        size_t descriptor_top = bucket->descriptor_top;

        if (descriptor_top == top)
                return search_descriptor(&bucket->descriptor, middle);

        if (-1UL == descriptor_top) return NULL;

        size_t ndescriptors = bucket->ndescriptors;

        size_t i;

        for (i = 0; i < ndescriptors; i++) {
                if (top == bucket->tops[i])
                        return search_descriptor
                                (bucket->descriptors+i, middle);
        }

        return NULL;
}

extern table_value_t
hash_table_set (table_t * table, size_t addr, table_value_t value)
{
        size_t hash = hash_address(addr) & (HASH_TABLE_SIZE-1);
        size_t top  = addr >> LOW_BITS;
        size_t middle = (addr >> BOTTOM_BITS) & ((1UL << MIDDLE_BITS)-1);

        bucket_t * bucket = table->buckets+hash;

        if (-1UL == bucket->descriptor_top) {
                bucket->descriptor_top = top;
                init_descriptor(&bucket->descriptor, middle, value);
                return 0;
        }

        if (top == bucket->descriptor_top)
                return descriptor_add(&bucket->descriptor, middle, value);

        size_t ndescriptors = bucket->ndescriptors;

        size_t empty_index = -1UL;
        size_t i;

        for (i = ndescriptors; i != 0; i--) {
                size_t ii = i - 1;
                if (top == bucket->tops[ii]) {
                        bucket->ndescriptors = ndescriptors;
                        return descriptor_add(&bucket->descriptors[ii],
                                              middle, value);
                }
                else if (-1UL == bucket->tops[ii]) {
                        empty_index = ii;
                        ndescriptors -= (ndescriptors == i) ? 1 : 0;
                }
        }

        bucket->ndescriptors = ndescriptors;

        if ((empty_index == -1UL)
            && (ndescriptors >= bucket->max_descriptors)) {
                size_t new_max = ndescriptors*2;
                new_max = (new_max < 2) ? 2 : new_max;

                bucket->tops = realloc(bucket->tops, new_max*sizeof(size_t));
                bucket->descriptors
                        = realloc(bucket->descriptors,
                                  new_max*sizeof(page_descriptor_t));
                bucket->max_descriptors = new_max;
                empty_index = ndescriptors;
                bucket->ndescriptors++;
        }

        bucket->tops[empty_index] = top;
        init_descriptor(&bucket->descriptors[empty_index], middle, value);

        return 0;
}

extern table_value_t
hash_table_del (table_t * table, size_t addr)
{
        size_t hash = hash_address(addr) & (HASH_TABLE_SIZE-1);
        size_t top  = addr >> LOW_BITS;
        size_t middle = (addr >> BOTTOM_BITS) & ((1UL << MIDDLE_BITS)-1);

        bucket_t * bucket = table->buckets+hash;

        if (-1UL == bucket->descriptor_top)
                return 0;

        if (top == bucket->descriptor_top) {
                table_value_t old
                        = descriptor_del(&bucket->descriptor, middle);
                if (old && !bucket->descriptor.values)
                        bucket->descriptor_top = -1UL;
                return old;
        }

        size_t ndescriptors = bucket->ndescriptors;

        size_t i;
        for (i = 0; i < ndescriptors; i++) {
                if (top == bucket->tops[i]) {
                        table_value_t old
                                = descriptor_del(&bucket->descriptors[i],
                                                 middle);
                        if (old && !bucket->descriptors[i].values)
                                bucket->tops[i] = -1UL;
                        return old;
                }
        }

        return 0;
}

#ifdef _TEST_HASH_TABLE_
#define N_ENTRIES_TEST (1UL << 8)

int main ()
{
        size_t i;
        size_t * keys = calloc(N_ENTRIES_TEST, sizeof(size_t));
        table_t * table = make_table();

        for (i = 0; i < N_ENTRIES_TEST; i++)
                keys[i] = (size_t)malloc(1UL<<LOW_BITS);

        double max_time = 0.0;
        double min_time = 1.0/0.0;
        double total_time = 0;

        double overhead = 0;

        const size_t reps = 16;

        for (i = 0; i < N_ENTRIES_TEST; i+= reps) {
                ticks begin = getticks();
                ticks end = getticks();

                overhead += elapsed(end, begin);
        }

        overhead = (overhead/N_ENTRIES_TEST)*reps;

        for (i = 0; i < N_ENTRIES_TEST; i+=reps) {
                ticks begin = getticks();
                for (size_t j = 0; j < reps; j++) {
                        //assert(!hash_table_get(table, key));
                        hash_table_set(table, keys[i+j], i+j);
                }
                ticks end = getticks();

                double delta = elapsed(end, begin) - overhead;
                total_time += delta;
                if (delta > max_time) max_time = delta;
                if (delta < min_time) min_time = delta;

                //printf("%f\n", delta/reps);
        }

        printf("insert: %f %f %f\n",
               min_time/reps,
               total_time/N_ENTRIES_TEST,
               max_time/reps);

        max_time = 0.0;
        min_time = 1.0/0.0;
        total_time = 0;

        for (i = 0; i < N_ENTRIES_TEST; i+=reps) {
                ticks begin = getticks();
                for (size_t j = 0; j < reps; j++)
                        if (i+j != *hash_table_get(table, keys[i+j])) {
                                printf("%lu -> %lu (%lu)\n",
                                       keys[i+j],
                                       (size_t) hash_table_get(table,
                                                               keys[i+j]),
                                       i+j);
                        }
                ticks end = getticks();

                double delta = elapsed(end, begin) - overhead;

                total_time += delta;
                if (delta > max_time) max_time = delta;
                if (delta < min_time) min_time = delta;

                //printf("%f\n", delta/reps);
        }

        printf("read: %f %f %f\n",
               min_time/reps,
               total_time/N_ENTRIES_TEST,
               max_time/reps);

        max_time = 0.0;
        min_time = 1.0/0.0;
        total_time = 0;

        for (i = 0; i < N_ENTRIES_TEST; i+=reps) {
                ticks begin = getticks();
                for (size_t j = 0; j < reps; j++)
                        if (i+j != hash_table_del(table, keys[i+j])) {
                                printf("%lu -> %lu (%lu)\n",
                                       keys[i+j],
                                       (size_t) hash_table_get(table,
                                                               keys[i+j]),
                                       i+j);
                        }
                ticks end = getticks();

                double delta = elapsed(end, begin) - overhead;

                total_time += delta;
                if (delta > max_time) max_time = delta;
                if (delta < min_time) min_time = delta;

                //printf("%f\n", delta/reps);
        }

        printf("del: %f %f %f\n",
               min_time/reps,
               total_time/N_ENTRIES_TEST,
               max_time/reps);

        max_time = 0.0;
        min_time = 1.0/0.0;
        total_time = 0;

        for (i = 0; i < N_ENTRIES_TEST; i+=reps) {
                ticks begin = getticks();
                for (size_t j = 0; j < reps; j++) {
                        size_t * ptr = hash_table_get(table, keys[i+j]);
                        if (ptr && *ptr) {
                                printf("%lu -> %lu (%lu)\n",
                                       keys[i+j],
                                       * hash_table_get(table,
                                                        keys[i+j]),
                                       0UL);
                        }
                }
                ticks end = getticks();

                double delta = elapsed(end, begin) - overhead;

                total_time += delta;
                if (delta > max_time) max_time = delta;
                if (delta < min_time) min_time = delta;

                //printf("%f\n", delta/reps);
        }

        printf("check: %f %f %f\n",
               min_time/reps,
               total_time/N_ENTRIES_TEST,
               max_time/reps);

        return 0;
}
#endif
