#define N 512
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
    for (int i = 0; i < N; i++){
        if (data[i] < best){
            best = data[i];
        }
    }
    return best;
}

void match_decomposed(int *db, int *OUTPUT_matches, int len, int *sample) {
  for(int i = 0; i < N; i++) {
    OUTPUT_matches[i] = match_fix(db[i*K], db[i*K+1], db[i*K+2], db[i*K+3], sample[0], sample[1], sample[2], sample[3]);
  }
}

int main( __attribute__((private(0))) int db[N*K], __attribute__((private(1))) int sample[4])
{
    //int matches[4];
    int matches[N];

    match_decomposed(db, matches, N, sample);
    // Compute minimum
    int best_match = min(matches, N);
    return best_match;
}