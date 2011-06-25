#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "store_buffer.h"
#include "gencgc-internal.h"

struct store_buffer store_buffer;

typedef struct store_buffer * store_buffer_t;

void init_store_buffer (store_buffer_t buffer, unsigned long count)
{
        memset(buffer, 0, sizeof(*buffer));
}
