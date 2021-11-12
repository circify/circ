int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int arr[4] = {a,b,a,b};
    int new_arr[4];
    for (int i = 0; i < 4; i++) {
        new_arr[i] = arr[i];
    }
    return new_arr[0];
}