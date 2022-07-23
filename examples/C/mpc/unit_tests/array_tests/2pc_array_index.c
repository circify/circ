int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int index = a + b;
    int arr[10] = {0, a, 2, 3, 4, 5, 6, 7, 8, 9};
    return arr[index] + arr[1];
}