#define SIZE_1 32
#define SIZE_2 1024

int contains(int pset[SIZE_2], int target) {
    int result = 0;
    for(int i = 0; i < SIZE_2; i++){
        int old_result = result;
        if(pset[i] == target){
            result = 1;
        } else{
            result = old_result;
        }
    }
    return result;
}


int main(__attribute__((private(0))) int pset1[SIZE_1], __attribute__((private(1))) int pset2[SIZE_2]) {
    int intersection[SIZE_1];
    for(int i = 0; i < SIZE_1; i++) {
        int result = contains(pset2, pset1[i]);
        intersection[i] = result;
    }
    int sum = 0;
    for (int i = 0; i < SIZE_1; i++){
        sum += intersection[i];
    }
    return sum;
}