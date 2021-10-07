int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int v[5];
    v[0] = a;
    b = v[0];
    return b;
}