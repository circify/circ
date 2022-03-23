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

// int min_(int * y) {
// 	int res = 0;
// 	for(int i = 0; i < 4; i++){
// 		res += y[i];
// 	}
//     return res;
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
//     int x[2][4];
//     x[0][0] = a;
//     x[0][1] = b;
//     x[0][2] = a;
//     x[0][3] = b;
//     x[1][0] = a;
//     x[1][1] = b;
//     x[1][2] = a;
//     x[1][3] = b;

//     int c[1];
//     c[0] = min_(x[0]); 
//     int res = c[0];	
//     return res;
// }

#define N 256
#define K 4 // currently fixed, do not change

#define INNER 64
#define OUTER (N/64)


int match_fix(int x1, int x2,int x3, int x4, int y1, int y2, int y3, int y4) {
  int r = 0;
  int i;
  int t1 = (x1-y1);
  int t2 = (x2-y2);
  int t3 = (x3-y3);
  int t4 = (x4-y4);
  r = t1*t1 + t2*t2 + t3*t3 + t4*t4;
  return r;
}

int min(int *data, int len) {
	int best = data[0];
    for (int i = 0; i < len; i++){
        if (data[i] < best){
            best = data[i];
        }
    }
    return best;
}

void match_decomposed(int *db, int *OUTPUT_matches, int len, int *sample) {
  for(int i = 0; i < len; i++) {
    OUTPUT_matches[i] = match_fix(db[i*K], db[i*K+1], db[i*K+2], db[i*K+3], sample[0], sample[1], sample[2], sample[3]);
  }
}

int main( __attribute__((private(0))) int db[1024], __attribute__((private(1))) int sample[4])
{
    //int matches[4];
    int matches[N];

    match_decomposed(db, matches, N, sample);
    // Compute minimum
    int best_match = min(matches, N);
    return best_match;
}