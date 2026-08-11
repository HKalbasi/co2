//@ mode: c
//@ run-status: 0

int main(void) {
    unsigned char a = 200;

    if (-(int)a != -200) return 1;
    if (-a != -200) return 2;
    if (~a != -201) return 3;
    if (+a != 200) return 4;

    char c = 100;
    if (c + c != 200) return 5;
    if (c - 150 != -50) return 6;

    signed char sc = -5;
    if (-sc != 5) return 7;
    if (~sc != 4) return 8;

    short s = 30000;
    if (-s != -30000) return 9;
    if (~s != -30001) return 10;

    return 0;
}
