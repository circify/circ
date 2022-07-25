#define LEN  32
#define NUM_REVIEWERS 1
#define NUM_RATINGS 1
#define INTERVALS 2
#define NUM_BUCKETS (INTERVALS * 5) - 1
#define TOTAL_REV (NUM_REVIEWERS * NUM_RATINGS)


int main(__attribute__((private(0))) int reviews[TOTAL_REV], __attribute__((private(1))) int offset)
{
  int result[NUM_BUCKETS];

  for (int i = 0; i < NUM_REVIEWERS; i++) {
      int sum = 0;
      for (int j = 0; j < NUM_RATINGS; j++) {
          sum = sum + reviews[i*NUM_RATINGS + j];
      }
      int bucket = sum;
      for (int j = 0; j < NUM_BUCKETS; j++) {
          int temp;
          if (j == bucket) {
              temp = result[j] + 1;
          }
          else {
              temp = result[j];
          }
          result[j] = temp;
      }
  }
  int sum_all = offset;
  for(int i = 0; i < NUM_BUCKETS; i++){
      sum_all += result[i];
  }
  return sum_all;
}


// int f(int a) {
//   return a + 1;
// }

// int main( __attribute__((private(0))) int a, __attribute__((private(1))) int b)
// {
//   // base input 
//   int c = f(a);
//   int d = f(b);

//   // add input
//   int e = a + c;
//   int g = b + d;
//   int h = f(e);
//   int i = f(g);

//   // multiply input 
//   int j = a * h;
//   int k = b * i;
//   int l = f(j);
//   int m = f(k);

//   return l + m;
// }
