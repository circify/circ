int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int c[2] = {0, 0};
    int * d = c;
    (d+0)[0] = a;
    (d+1)[0] = b;
    return c[0] + c[1];
}