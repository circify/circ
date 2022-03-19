// struct s {
// 	int c[4];
// };

// void f(int* x, int* y) {
//     int c;
//     for (c = 0; c < 4; c++) {
//         y[c] = x[c];
//     }
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
//     int x[4] = {a,b,a,b};

//     struct s y; 
//     f(x, y.c);

//     int sum = 0;
//     for (int i = 0; i < 4; i++) {
//         sum += y.c[i];
//     }
//     return sum;
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
//     int x[1][4];
//     x[0][0] = a;
//     x[0][1] = b;
//     x[0][2] = a;
//     x[0][3] = b;

//     int sum = 0;
//     for (int i = 0; i < 4; i++) {
//         sum += x[0][i];
//     }
//     return sum;
// }

int min_(int * y) {
	int res = 0;
	for(int i = 0; i < 4; i++){
		res += y[i];
	}
    return res;
}

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    int x[2][4];
    x[0][0] = a;
    x[0][1] = b;
    x[0][2] = a;
    x[0][3] = b;
    x[1][0] = a;
    x[1][1] = b;
    x[1][2] = a;
    x[1][3] = b;

    int c[1];
    c[0] = min_(x[0]); 
    int res = c[0];	
    return res;
}
