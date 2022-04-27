int t() {
    int i;
    if (0 == 0) {
        i = 10;
    } else {
        i = 20;
    }
    return i;
}

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
	return t();
} 