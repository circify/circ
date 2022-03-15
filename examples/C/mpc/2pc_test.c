int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int arr[1][4] = {{a,b,a,b}};
    return arr[0];
}