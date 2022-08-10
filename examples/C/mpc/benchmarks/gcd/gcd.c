int LEN = 32;
int main( __attribute__((private(0))) int a, __attribute__((private(1))) int b) {
    int gcd = 0;
    for (int i = 0; i < LEN; i++) {
        if (b != 0){
            gcd = a % b;
            int temp = b;
            b = gcd;
            a = temp;
        } else{
            gcd = a;
        }
    }
    return gcd;
}