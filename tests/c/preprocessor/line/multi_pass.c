//@ mode: c
//@ run-status: 0

#include <assert.h>
#include "./multi_pass.h"

int main() {
    assert(f1() == 6);
    assert(f2() == 12);
    int line = __LINE__;
    assert(line == 11);
    return 0;
}
