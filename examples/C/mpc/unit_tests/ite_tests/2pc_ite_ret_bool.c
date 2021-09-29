#include <stdbool.h>

bool main(__attribute__((private(0))) bool a, __attribute__((private(1))) bool b,  __attribute__((public)) bool sel) { 
    if (sel) {
        return a;
    } else {
        return b;
    }
}
