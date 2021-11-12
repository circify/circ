int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    // int arr[2];
    // for (i = 0; i < 2; i++) {
    //     arr[i] = i+1;
    // }
    // int acc = 0;
    // for (i = 0; i < 2; i++) {
    //     acc += arr[i];
    // }
    // return acc;
    int arr[2];
    for (int i = 0; i < 2; i++) arr[i] = i;
    // int acc = 0;
    // for (int j = 0; j < 2; j++) acc += arr[j];
    // return acc;
    int acc = 0;
    int j;
    for (j = 0; j < 2; j++) {
        acc += arr[j];
    }
    return acc;
}