int len = 32;

int rem(int x, int y){
    int rem = 0;
    for (int j = 0; j < len; j++){
        
        rem = rem << 1;
        rem = rem + ((x >> (len - j - 1)) & 1);

        int rem2 = rem - y;
        if (rem >= y){
            rem = rem2;
        }
    }
    return rem;
}
  
int main( __attribute__((private(0))) int a, __attribute__((private(1))) int b)
{
    //int matches[4];
    int gcd = 0;
    for (int i = 0; i < len; i++){
        gcd = rem(a, b);
        int temp = b;
        if (b < 0){
            b = gcd;
            a = temp;
            gcd = 1;
        }
    }
    return gcd;
}