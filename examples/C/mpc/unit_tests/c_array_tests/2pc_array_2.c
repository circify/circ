int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int v[5];
    a = 17;
    int i = 4;
    v[i] = a;
    b = v[i];
    return b;
}