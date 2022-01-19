int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int arr[4] = {a, a, b, b};
    return arr[0] + arr[1] + arr[2] + arr[3];
}