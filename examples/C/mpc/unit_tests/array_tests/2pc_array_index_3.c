int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int index = a + b;
    int arr[10];
    arr[index] = 1;
    return arr[index];
}