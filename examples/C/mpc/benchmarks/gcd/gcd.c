#include <stdio.h>

int len = 32;

int rem(int x, int y){
    int rem = 0;
    for (int j = len - 1; j >= 0; j--){
        rem = rem << 1;
        rem = rem + ((x >> j) & 1);

        int rem2 = rem - y;
        if (rem >= y){
            rem = rem2;
        }
        // printf("hello\n");
    }
    return rem;
}
  
int main()
{
    //int matches[4];
    int a = 3571;
    int b = 3559;
    int gcd = 0;
    for (int i = 0; i < len; i ++){
        gcd = rem(a, b);
        int temp = b;
        if (b != 0){
            b = gcd;
            a = temp;
        }
        // printf("GCD for %d and %d is %d\n", a, b, gcd);
    }
    printf("GCD for %d and %d is %d\n", a, b, gcd);
    return gcd;
}