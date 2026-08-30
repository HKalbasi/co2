//@ mode: c
//@ run-status: 0
// Test for thread-local storage (_Thread_local / thread_local) in C11/C23.

#include <stddef.h>
#include <assert.h>
#include <threads.h>
#include <stdatomic.h>   // for atomic int to coordinate

// ------------------------------------------------------------
// 1. Basic thread-local variable declarations
// ------------------------------------------------------------

static _Thread_local int tls_counter = 0;            // static TLS, initialized to 0
static thread_local int tls_alt = 1;                // using macro from <threads.h>

// Extern declaration (definition elsewhere, but we will define it)
extern _Thread_local long tls_long;

_Thread_local long tls_long = 100;                  // definition with initializer

// TLS with type qualifiers (const, volatile)
static _Thread_local const int tls_const = 5;       // read-only in each thread
static _Thread_local volatile int tls_volatile = 0;

// TLS with array type
static _Thread_local int tls_array[4] = {1, 2, 3, 4};

// TLS with struct
struct data { int a; double b; };
static _Thread_local struct data tls_struct = { .a = 10, .b = 3.14 };

// ------------------------------------------------------------
// 2. Helper: thread function that manipulates TLS and reports
// ------------------------------------------------------------

// Use a global atomic counter to know how many threads have finished
atomic_int thread_count = 0;

int thread_func(void *arg) {
    int id = *(int*)arg;

    // Each thread sees its own copy of tls_counter
    tls_counter = id;                     // set to thread ID
    tls_counter += 10;                    // modify
    assert(tls_counter == id + 10);

    // tls_alt starts at 1 per thread
    assert(tls_alt == 1);
    tls_alt = id * 2;
    assert(tls_alt == id * 2);

    // tls_long (extern) – per thread, starts at 100
    assert(tls_long == 100);
    tls_long += id;
    assert(tls_long == 100 + id);

    // const TLS: cannot modify, but we can read
    assert(tls_const == 5);

    // volatile TLS – read/write
    tls_volatile = id;
    assert(tls_volatile == id);

    // Array TLS – each thread gets its own copy
    for (int i = 0; i < 4; i++) {
        tls_array[i] += id;
        assert(tls_array[i] == (i + 1) + id);
    }

    // Struct TLS
    tls_struct.a += id;
    tls_struct.b += id;
    assert(tls_struct.a == 10 + id);
    assert(tls_struct.b == 3.14 + id);

    // Signal completion
    atomic_fetch_add(&thread_count, 1);
    return 0;
}

// ------------------------------------------------------------
// 3. Main: spawn threads and verify independence
// ------------------------------------------------------------

int main(void) {
    enum { NUM_THREADS = 5 };
    thrd_t threads[NUM_THREADS];
    int ids[NUM_THREADS];

    // Spawn threads
    for (int i = 0; i < NUM_THREADS; i++) {
        ids[i] = i + 1;           // IDs 1..5
        if (thrd_create(&threads[i], thread_func, &ids[i]) != thrd_success) {
            return 1;
        }
    }

    // Wait for all threads to finish
    for (int i = 0; i < NUM_THREADS; i++) {
        int res;
        thrd_join(threads[i], &res);
        assert(res == 0);
    }

    // All threads have completed
    assert(atomic_load(&thread_count) == NUM_THREADS);

    // ------------------------------------------------------------
    // 4. Verify main thread's TLS values remained unchanged
    //    (main also has its own copies)
    // ------------------------------------------------------------
    assert(tls_counter == 0);      // main's counter was never modified
    assert(tls_alt == 1);
    assert(tls_long == 100);
    assert(tls_const == 5);
    assert(tls_volatile == 0);

    for (int i = 0; i < 4; i++) {
        assert(tls_array[i] == i + 1);
    }

    assert(tls_struct.a == 10);
    assert(tls_struct.b == 3.14);

    return 0;
}
