int foo(int a){
    return a + 1;
}

int bar(int b){
    return b * 2;
}

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
    return foo(a) - bar(b);
}
