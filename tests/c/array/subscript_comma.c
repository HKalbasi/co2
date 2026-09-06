//@ mode: c
//@ run-status: 0

// Comma expression inside subscript without parens: a[i++, 2] means a[(i++, 2)].

int main() {
    int a[3] = {10, 20, 30};
    int i = 0;
    if (a[i++, 2] != 30) {
        return 1;
    }
    if (i != 1) {
        return 2;
    }
    return 0;
}
