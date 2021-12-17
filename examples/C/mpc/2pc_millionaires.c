int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
   int res = a;
   if (a < b) {
      res = b;
   }
   return res;
}