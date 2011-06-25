#ifndef _STORE_BUFFER_H_
#define _STORE_BUFFER_H_
#include "sbcl.h"
#include "runtime.h"

struct store_buffer {
        unsigned char table[BACKEND_CARD_TABLE_SIZE];
};

extern struct store_buffer store_buffer;
void init_store_buffer (struct store_buffer *, unsigned long count);
#endif
