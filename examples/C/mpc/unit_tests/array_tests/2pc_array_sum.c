int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int c[2][5][6];
    int arr[2] = {a, b};
    return arr[0] + arr[1];
}