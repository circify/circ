int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int c[1];
    if (a < b) {
        c[0] = 1;
    }
    return c[0];
}