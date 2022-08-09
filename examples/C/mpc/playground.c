void foo(int* x){
  x[0] += 1;
  x[1] += 1;
}

int main(__attribute__((private(0))) int a[2], __attribute__((private(1))) int b[2]) { 
  foo(a);
  foo(b);
  return a[0] + b[0];
}