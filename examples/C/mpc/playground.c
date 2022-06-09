#define LEN 1

int fa(int * c, int a) {
    for (int i = 0; i < LEN; i++) {
        c[i] = c[i] + a;
    }
    return 1;
}

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
    int c[LEN];
    int ret = fa(c, a);
    int sum = ret;
    for (int i = 0; i < LEN; i++) {
        sum += c[i];
    }
    return sum;
}

// int fa(int a, int b, int c) {
//     return a + b + c + 1;
// }

// int fb(int a) {
//     return fa(a, a, a);
// }

// int fc(int a) {
//     return fb(a);
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
//     int c = fc(a) + fc(b); 
//     return c;
// }