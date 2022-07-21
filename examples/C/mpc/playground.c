int foo(int* a){
    return a[0] + a[1];
}

int bar(int* b){
    return b[0] * b[1];
}

int main(__attribute__((private(0))) int a[2], __attribute__((private(1))) int b[2]) {
    return foo(a) + bar(b);
}
