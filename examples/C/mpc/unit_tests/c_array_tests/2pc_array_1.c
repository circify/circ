int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int v[5];
    a = 17;
    v[1] = a;
    b = v[1];
    return b;
}