int foo(int* x){
  int ret = 0;
  for(int i = 0; i < 4; i++){
    ret += x[i];
  }
  return ret;
}

int main(__attribute__((private(0))) int a[4], __attribute__((private(1))) int b) { 
  return foo(a) + b;
}