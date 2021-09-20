// do you parse me?
#include "test.h"

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
   return a + b;
}