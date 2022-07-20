int f(int * a) {
  a[0] += 1;
  return a[0] + 1;
}

int main( __attribute__((private(0))) int a, __attribute__((private(1))) int b)
{
   int c[1] = {1};
   int d = f(c);
   return d + c[0];
}