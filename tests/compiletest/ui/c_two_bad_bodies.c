//@ mode: c
//@ compile-fail

int first(void) {
    return missing_first;
    //     ^^^^^^^^^^^^^ error: Unresolved name
}

int second(void) {
    return missing_second;
    //     ^^^^^^^^^^^^^^ error: Unresolved name
}
