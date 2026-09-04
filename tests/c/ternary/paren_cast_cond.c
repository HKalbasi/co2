//@ mode: c
//@ run-status: 0

// Reproducer: a parenthesized relational comparison with a cast operand
// as a ternary condition is rejected with
// "int is invalid as Rust type" (seen when compiling sqlite3.c, where
// ALWAYS(i<BMS) expands to such a condition). Valid C; gcc accepts it.
// Note: the bug needs a non-constant LHS and the parens; without either,
// co2cc currently accepts the code.

int main(void) {
    int i = 3;
    int m = (i < (int)8) ? 1 : 0;
    return m == 1 ? 0 : 1;
}
