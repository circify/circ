int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
   int c = a * b;
   for (int i = 0; i < 10000; i++) {
      c = c * a;
   }
   return c;
}