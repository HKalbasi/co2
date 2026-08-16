//@ mode: c
//@ run-status: 0

use std::vec::Vec;
use std::mem::drop;

#include <assert.h>

int main() {
    auto x = Vec::<i32>::new();
    x.push(4);
    assert(x.len() == 1);

    drop(x);

    return 0;
}
