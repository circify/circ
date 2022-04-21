int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
	int sum = a + b;
	for (int i = 5; i >= 0; i--) {
		sum += i;
	}
	return sum;
}