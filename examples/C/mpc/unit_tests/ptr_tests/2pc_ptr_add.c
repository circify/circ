int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int c[1][2] = {{a, b}};
    int * d = c[0];
    return d[0] + d[1];
}