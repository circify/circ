int main(__attribute__((private(0))) int a[5], __attribute__((private(1))) int b[5]) { 
    int sum[5];
    for (int i = 0; i < 5; i++) {
        sum[i] = a[i] + b[i];
    }
    int acc = 0;
    for (int j = 0; j < 5; j++) {
        acc += sum[j];
    }
    return acc;
}