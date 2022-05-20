int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int c[1][2];
    c[0][0] = a;
    c[0][1] = b;
    return c[0][0] + c[0][1];
}