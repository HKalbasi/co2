//@ mode: c
//@ run-status: 0

#include <stddef.h>

typedef size_t strlen_func(const char*);
typedef void *malloc_func(size_t);

strlen_func strlen;
malloc_func malloc;

int main() {
    if (strlen("foo") != 3) {
        return 1;
    }
    int *p = (int*)malloc(4);
    return 0;
}
