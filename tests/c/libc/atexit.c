//@ mode: c
//@ run-status: 0
//@ run-stdout: in main\nExiting!\n

#include <stdlib.h>
#include <stdio.h>

static void foo(){
    printf("Exiting!\n");
}

int main(){
    atexit(foo);
    printf("in main\n");
    return 0;
}
