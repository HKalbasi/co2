//@ mode: c
//@ run-status: 0

typedef int fn;

fn foo() {
    return 5;
}

int foo2() {
    int u64 = 64;
    return u64;
}

//* Some comment
/// Some comment
//! Some comment
int main() {
    if (foo() != 5) {
        return 1;
    }
    //* Some comment
    /// Some comment
    //! Some comment
    if (foo2() != 64) {
        return 2;
    }
    return 0;
}
