int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    // int arr[2] = {a, b};
    // return arr[0] + arr[1];
    int c[2][2] = {{a, b}, {a, b}};
    return c[0][0] + c[1][1];
}