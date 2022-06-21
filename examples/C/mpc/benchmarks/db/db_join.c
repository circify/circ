/**
 * Example on how to merge two data sets and to perform various analyses
 */

#define LEN_A 5
#define LEN_B 5

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


/*int join(DT *OUTPUT_db, DT *a, DT *b, int len_a, int len_b, int att_a, int att_b) {
	int id_a = 0;
	int id_b = 0;
	int id_out = 0;
	int att_out = att_a + att_b - 1;
	for(int i = 0; i < len_a + len_b && id_a < len_a && id_b < len_b; i++) {
		if(a[id_a] == b[id_b]) { // Compare first element
			OUTPUT_db[id_out*att_out] = a[id_a*att_a];
			OUTPUT_db[id_out*att_out+1] = a[id_a*att_a+1];
			OUTPUT_db[id_out*att_out+2] = b[id_b*att_b+1];
			//memcpy(OUTPUT_db + id_out * att_out, a+id_x*att_a, att_a);
			//memcpy(OUTPUT_db + id_out * att_out + att_a, a+id_x*att_a, att_a);
			id_a++;
			id_b++;
			id_out++;
		} else if (id_a > id_b) {
			id_b++;
		} else {
			id_a++;
		}
	}
	return id_out;
} */


DT agg_mean_tree(DT *db, int len, int att) {
	DT sum[len];
	for(int i = 0; i < len; i++) {
		sum[i] = db[i*att+1] + db[i*att+2];
	}
	DT mean = sum_tree(sum, len, 1);
	int joined = db[len*att];
	int ret;
	if(joined > 0) {
		ret = mean/joined;
	} else {
		ret = 0;
	}
	return ret;
}

DT agg_mean(DT *db, int len, int att) {
	DT sum[len];
	for(int i = 0; i < len; i++) {
		sum[i] = db[i*att+1] + db[i*att+2];
	}
	return mean_with_abort(sum, len);
}

int main(__attribute__((private(0))) int a[LEN_A*ATT_A], __attribute__((private(1))) int b[LEN_B*ATT_B]) {
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
	//res.analysis2 = variance(db, LEN_A*LEN_B);
	return res.joined + res.analysis1 + res.analysis2;
} 
