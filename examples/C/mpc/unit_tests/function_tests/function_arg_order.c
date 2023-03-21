int sub(int b, int a) {
    return a - b;
}

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
   return sub(b, a);
}