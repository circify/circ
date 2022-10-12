int test(int a, int b) {
    if (11 > 10) {
       return 1;
    } else{
       return 2;
    }
}


int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
    int c = test(a, b); 
    return c;
}