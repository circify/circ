#include <stdbool.h>

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b,  __attribute__((public)) bool sel) { 
    if (sel) {
        return a;
    } else {
        return b;
    }
}
