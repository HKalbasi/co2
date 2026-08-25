//@ mode: c
//@ run-status: 0

#include <stdio.h>
#include <stdint.h>
#include <sys/syscall.h>
#include <sys/param.h>

int main(void) {
    printf("Hello from co2cc isolated!\n");
    return 0;
}
