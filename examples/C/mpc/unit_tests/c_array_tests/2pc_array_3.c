int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int v[3];
    for (int i = 0; i < 3; i++) v[i] = a + b + i;
    int acc = 0;
    for (int j = 0; j < 3; j++) acc += v[j];
    return acc;
}