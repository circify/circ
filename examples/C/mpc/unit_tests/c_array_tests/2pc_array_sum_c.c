int main(__attribute__((private(0))) int a[2], __attribute__((private(1))) int b[2]) { 
    int sum[2];
    for (int i = 0; i < 2; i++) {
        sum[i] = a[i] + b[i];
    }
    int acc = 0;
    for (int j = 0; j < 2; j++) {
        acc += sum[j];
    }
    return acc;
}