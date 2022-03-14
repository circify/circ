int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int arr[4][1] = {{a,b,a,b}};
    return arr[0];
}