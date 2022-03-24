int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int c[1][2];
    int * d = c[0];
    d[0] = a;
    d[1] = b;
    return c[0][0] + c[0][1];
}