//@ mode: c
//@ run-status: 0
#pragma once

inline int f1() {
    return __LINE__;
}

#define FOO __LINE__

inline int f2() {
    return FOO;
}

  #warning warn1
// ^^^^^^^ warning: #warning warn1

// Some text
// ^^^^^^^ warning: #warning warn2

// Other text that is longer
                // ^ warning: function returns without a value

#line 18
  #warning warn2


inline int warn3() {}
