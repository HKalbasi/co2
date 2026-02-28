//@ mode: c
//@ ui-error: Failed to resolve type

typedef struct {
  union {

    struct {
      void *_lower;
      void *_upper;
    } _addr_bnd;

    unknown_type _pkey;
  } _bounds;
} _sigfault;

int main(void) { return 0; }
