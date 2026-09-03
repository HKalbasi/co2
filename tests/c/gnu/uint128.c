//@ mode: c
//@ run-status: 0

int main(void) {
    __uint128_t r = (__int128_t)3 * 4;
    return r == 12 ? 0 : 1;
}
