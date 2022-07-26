int  main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
  int c = a * b;
  return c + a;
}


// int f(int a) {
//   return a + 1;
// }

// int main( __attribute__((private(0))) int a, __attribute__((private(1))) int b)
// {
//   // base input 
//   int c = f(a);
//   int d = f(b);

//   // add input
//   int e = a + c;
//   int g = b + d;
//   int h = f(e);
//   int i = f(g);

//   // multiply input 
//   int j = a * h;
//   int k = b * i;
//   int l = f(j);
//   int m = f(k);

//   return l + m;
// }