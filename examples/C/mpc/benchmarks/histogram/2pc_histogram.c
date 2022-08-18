#define LEN  32
#define NUM_REVIEWERS 100
#define NUM_RATINGS 100
#define INTERVALS 2
#define NUM_BUCKETS (INTERVALS * 5) - 1
#define TOTAL_REV (NUM_REVIEWERS * NUM_RATINGS)


/* returns val/mod, integer division */
// int quot(int val, int mod) {
//     if (mod == 0){
//         return val;
//     } else{
//         int rem = val % mod;
//         return (val - rem) / mod;
//     }
// }

int map(int sumRatings) {

    int bucket = NUM_RATINGS+1;

    int val = sumRatings;
    int mod = NUM_RATINGS;

    int absReview = val / mod;
    int fraction = val % mod;

    int m = INTERVALS * (absReview - 1);
    int num = fraction * INTERVALS;
    for (int j = 0; j < INTERVALS; j++) {
        int low = j * NUM_RATINGS;
        int high = (j + 1) * NUM_RATINGS;
        int cond1;
        if(low <= num) {
            cond1 = 1;
        }
        else {
            cond1 = 0;
        }
        int cond2;
        if(high > num) {
            cond2 = 1;
        }
        else {
            cond2 = 0;
        }
        int cond = cond1 + cond2;
        
        int newBucket;
        if(cond == 2) {
            newBucket = m + j;
        }
        else {
            newBucket = bucket;
        }
        
        bucket = newBucket;
    }

    return bucket;
}

int main(__attribute__((private(0))) int reviews[TOTAL_REV], __attribute__((private(1))) int offset)
{
    int result[NUM_BUCKETS];
    for(int i = 0; i < NUM_BUCKETS; i ++){
        result[i] = 0;
    }
    for (int i = 0; i < NUM_REVIEWERS; i++) {
        int sum = 0;
        for (int j = 0; j < NUM_RATINGS; j++) {
            sum = sum + reviews[i*NUM_RATINGS + j];
        }
        int bucket = map(sum);
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
