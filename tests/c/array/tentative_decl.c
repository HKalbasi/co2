//@ mode: c
//@ run-status: 0
//@ run-stdout: 34567

#include <stdio.h>

#define NUM 32

int Array[];
int Array[NUM];
int Foo;
int main(){
    for (int i = 0; i < NUM; i++) Array[i]=i+3;
    for (int i = 0; i < 5; i++) printf("%d", Array[i]);
    return 0;
}
