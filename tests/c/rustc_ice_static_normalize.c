//@ mode: c
//@ compile-fail

// The function call inside the initializer list bypasses const evaluation
// in co2, reaching `lower_expr` which calls `normalize_ty_for_current_owner`.
// Without the fix this ICEs in generics_of (root crate's Node::Crate not handled).
// With the fix, rustc properly rejects the non-const fn call.

int non_const_fn(void) {
    return 42;
}

static int static_arr[] = { non_const_fn() };
                        //  ^^^^^^^^^^^^^^ error: cannot call non-const function `non_const_fn` in statics

int main() {
    return 0;
}
