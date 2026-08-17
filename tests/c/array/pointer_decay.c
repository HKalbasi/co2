//@ mode: c
//@ run-status: 0

static int array[3] = {1, 2, 3};
static int *ptr1 = &array[1];
static int *ptr0 = array;
static int (*ptr_to_ptr)[3] = &array;

int main() {
    if (array[1] != ptr1[0]) {
        return 1;
    }
    if (ptr0[2] != ptr1[1]) {
        return 2;
    }
    if ((*ptr_to_ptr)[2] != (*ptr_to_ptr)[1] + 1) {
        return 3;
    }
    return 0;
}
