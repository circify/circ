void bar(int *x){
  x[0] += 1;
  x[1] += 1;
}

void foo(int* x){
  bar(x);
}

int main(__attribute__((private(0))) int a[2], __attribute__((private(1))) int b[2]) { 
  foo(a);
  return a[0] + b[0];
}