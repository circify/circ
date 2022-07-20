/**
 * Example on how to merge two data sets and to perform various analyses
 */

#define LEN_A 20
#define LEN_B 20

#define ATT_A 2 //Number of attributes
#define ATT_B 2

#include "db.h"

int cross_join(DT *OUTPUT_db, DT *a, DT *b) {
	int id_a = 0;
	int id_b = 0;
	int id_out = 0;
	
	for(int i = 0; i < LEN_A*LEN_B*ATT+1; i++) {
		OUTPUT_db[i] = 0;//-1;
	}
	
	for(int i = 0; i < LEN_A; i++) {
		for(int j = 0; j < LEN_B; j++) {
			if(a[i*ATT_A] == b[j*ATT_B]) {
				OUTPUT_db[id_out*ATT] = a[i*ATT_A];
				OUTPUT_db[id_out*ATT+1] = a[i*ATT_A+1];
				OUTPUT_db[id_out*ATT+2] = b[j*ATT_B+1];
				id_out++;
			}
		}
	}
	
	return id_out;
}

int cross_join_trivial(DT *OUTPUT_db, DT *a, DT *b) {
	int id_a = 0;
	int id_b = 0;
	int id_out = 0;
	
	for(int i = 0; i < LEN_A*LEN_B*ATT+1; i++) {
		OUTPUT_db[i] = 0;//-1;
	}
	
	for(int i = 0; i < LEN_A; i++) {
		for(int j = 0; j < LEN_B; j++) {			
			if(a[i*ATT_A] == b[j*ATT_B]) {
				id_out++;
				OUTPUT_db[(i*LEN_B+j)*ATT] = a[i*ATT_A];
				OUTPUT_db[(i*LEN_B+j)*ATT+1] = a[i*ATT_A+1];
				OUTPUT_db[(i*LEN_B+j)*ATT+2] = b[j*ATT_B+1];
			}
		}
	}
	
	return id_out;
}

DT agg_mean_tree(DT *db, int len, int att) {
	DT sum[LEN_A*LEN_B];
	for(int i = 0; i < LEN_A*LEN_B; i++) {
		sum[i] = db[i*ATT+1] + db[i*ATT+2];
	}
	DT mean = sum_tree(sum, LEN_A*LEN_B, 1);
	int joined = db[LEN_A*LEN_B*ATT];
	int ret;
	if(joined > 0) {
		ret = mean/joined;
	} else {
		ret = 0;
	}
	return ret;
}

DT agg_mean(DT *db, int len, int att) {
	DT sum[LEN_A*LEN_B];
	for(int i = 0; i < LEN_A*LEN_B; i++) {
		sum[i] = db[i*ATT+1] + db[i*ATT+2];
	}
	return mean_with_abort(sum, len);
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

	DT db[LEN_A*LEN_B*ATT+1]; // +1 is an ugly hack to copy len into buffer
	
	// merge databases
	res.joined = cross_join(db, INPUT_A.db, INPUT_B.db);
	
	if(res.joined >= LEN_A*LEN_B) { // Limits the last element
		res.joined = LEN_A*LEN_B-1;
	}
	db[LEN_A*LEN_B*ATT] = res.joined;
	res.analysis1 = agg_mean_tree(db, LEN_A*LEN_B, ATT);
	res.analysis2 = res.analysis1;
	// res.analysis2 = variance(db, LEN_A*LEN_B);
	return res;
} 
