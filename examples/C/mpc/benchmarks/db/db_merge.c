/**
 * Example on how to merge two data sets and to perform various analyses
 */
 
#define LEN_A 100
#define LEN_B 100
#define ATT_A 1 //Number of attributes
#define ATT_B 1

#include "db.h"

void merge(DT *OUTPUT_db, DT *a, DT *b) {
	// memcpy(OUTPUT_db, a, len_a * sizeof(DT));
    for (int i = 0; i < LEN_A; i++) {
        OUTPUT_db[i] = a[i];
    }
	// memcpy(OUTPUT_db + len_a, b, len_b * sizeof(DT));
    for (int i = 0; i < LEN_B; i++) {
        (OUTPUT_db+LEN_A)[i] = b[i];
    }
} 

DT mean_(DT *db) {
	DT mean = sum_tree_(db);
	return mean/LEN;
}

DT sum_tree_(DT *data) {
	int sum = 0;
	for (int i = 0; i < LEN; i++) {
		sum += data[i];
	}
	return sum;
}

DT variance_(DT *db) {
	DT exp = mean_(db);
	DT var[LEN];// = 0;
	for(int i = 0; i < LEN; i++) {
		DT dist = db[i] - exp;
		var[i] = dist * dist;
		//var += dist;
	}
	DT res = sum_tree_(var);
	return res / LEN;
}

Output main(__attribute__((private(0))) int a[LEN_A*ATT_A], __attribute__((private(1))) int b[LEN_B*ATT_B]) {
    Output res;
    InputA INPUT_A;
    for (int i = 0; i < LEN_A*ATT_A; i++) {
        INPUT_A.db[i] = a[i];
    }
    InputB INPUT_B;
    for (int i = 0; i < LEN_B*ATT_B; i++) {
        INPUT_B.db[i] = b[i];
    }

    DT db[LEN];
    // merge databases
	merge(db, INPUT_A.db, INPUT_B.db);
	// compute? histogram, correlation or
	
	res.joined = LEN;
	// res.analysis1 = mean(db, LEN);
    res.analysis1 = mean_(db);
	// res.analysis2 = variance(db, LEN);
    res.analysis2 = variance_(db);

	return res;
}

