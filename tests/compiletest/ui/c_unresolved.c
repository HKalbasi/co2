//@ mode: c
//@ compile-fail

int f1() {
    missing;
  //^^^^^^^ error: Unresolved name missing
}

int f2() {
    missing x = 5;
  //^^^^^^^ error: Unresolved name missing
}

int f3() {
    int x = 2;
    x* y = &x;
     //^ error: Unresolved name y
}

int main() {
    return missing;
    //     ^^^^^^^ error: Unresolved name missing
}

#define SOME_MACRO 5

int f4() {
    return SOME_MACRO + missing;
                      //^^^^^^^ error: Unresolved name missing
}

#define BAD_MACRO 5 + missing

int f5() {
    return BAD_MACRO + 3;
         //^^^^^^^^^ error: Unresolved name missing
}

