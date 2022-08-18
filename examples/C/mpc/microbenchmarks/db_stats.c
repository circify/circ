#define INPUT_LEN 100
#define LEN (INPUT_LEN*2)

typedef struct
{
	int mean;
	int variance;
} Output;


int mean_(int * db) {
	int mean = 0;
	for (int i = 0; i < LEN; i++) {
		mean += db[i];
	}
	return mean/LEN;
}

int variance_(int * db) {
	int exp = mean_(db);
	int var[LEN]; 
	for(int i = 0; i < LEN; i++) {
		int dist = db[i] - exp;
		var[i] = dist * dist;
	}
	int res = mean_(var);
	return res;
}

Output main(__attribute__((private(0))) int a[INPUT_LEN], __attribute__((private(1))) int b[INPUT_LEN]) {
    Output res;

	int db[LEN*2];
    for (int i = 0; i < INPUT_LEN; i++) {
        db[i] = a[i];
    }
    for (int i = INPUT_LEN; i < LEN; i++) {
        db[i] = b[i];
    }

    res.mean = mean_(db);
    res.variance = variance_(db);
	return res;
}

