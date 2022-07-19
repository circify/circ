/**
 * Example on how to merge two data sets and to perform various analyses
 */

#define LEN_A 30
#define LEN_B 30

#define ATT_A 2 //Number of attributes
#define ATT_B 2

#include "db.h"

// DB[len][att] row[att]
int cross_join_inner(DT *OUTPUT_db, DT *db, DT *row) {
	int id_out = 0;
	
	int att_out = ATT_B*2-1;
	
	for(int i = 0; i < LEN_B*att_out; i++) {
		OUTPUT_db[i] = 0;
	}
	
	for(int i = 0; i < LEN_B; i++) {			
		if(db[i*ATT_B] == row[0]) {
			id_out++;
			OUTPUT_db[i*att_out] = db[i*ATT_B];
			OUTPUT_db[i*att_out+1] = db[i*ATT_B+1];
			OUTPUT_db[i*att_out+2] = row[1];
		}
	}
	return id_out;
}

int cross_join_decomposed(DT *OUTPUT_db, DT *a, DT *b) {
	int id_out = 0;
	
	DT zero[LEN_B*ATT];
	for(int i = 0; i < LEN_B*ATT; i++) {
		zero[i] = 0;
	}
	for(int i = 0; i < LEN_A; i++) {
		OUTPUT_db[i] = 0;//-1;
		// memcpy(&OUTPUT_db[i*LEN_B*ATT], zero, LEN_B*ATT*sizeof(DT));
        for (int j = 0; j < LEN_B*ATT; j++) {
            OUTPUT_db[i*LEN_B*ATT+j] = zero[j];
        }
	}
	
	for(int i = 0; i < LEN_A; i++) {
		DT row[ATT_B];
		row[0] = a[i*ATT_A];
		row[1] = a[i*ATT_A+1];
		DT tmp[LEN_B*ATT];
		// id_out += cross_join_inner(tmp, b, row, LEN_B, ATT_B);
        id_out += cross_join_inner(tmp, b, row);
		// memcpy(OUTPUT_db, tmp, LEN_B*ATT*sizeof(DT));
        for (int j = 0; j < LEN_B*ATT; j++) {
            OUTPUT_db[j] = tmp[j];
        }
		id_out += tmp[LEN_B+ATT];
	}
	OUTPUT_db[LEN_A*LEN_B*ATT] = id_out;
	return id_out;
}


DT sqr(DT val, DT exp) {
	DT dist = (val - exp) * (val - exp);
	return dist;
}

DT mean_(DT *db) {
    int sum = 0;
	for (int i = 0; i < LEN_B * ATT; i++) {
		sum += db[i];
	}
	return sum / (LEN_B * ATT);
}

DT sum_tree_a(DT *data) {
	int sum = 0;
	for (int i = 0; i < LEN_A; i++) {
		sum += data[i];
	}
	return sum;
}

DT sum_tree_b(DT *data) {
	int sum = 0;
	for (int i = 0; i < LEN_B; i++) {
		sum += data[i];
	}
	return sum;
}

DT agg_variance_sum(DT *db) {
	DT exp = mean_(db);
	DT var[LEN_B]; // = 0;
	for(int i = 0; i < LEN_B; i++) {
		if(db[i]!=0) {
			var[i] = sqr(db[i], exp);
		} else {
			var[i] = 0;
		}
	}
	DT res = sum_tree_b(var);
	return res;
}


DT agg_variance_decomposed(DT *db) {
	DT tmp[LEN_B*ATT];
	DT sum[LEN_A];
	for(int i = 0; i < LEN_A; i++) {
		// memcpy(tmp, &db[i*LEN_B*att],LEN_B*att*sizeof(DT));
        for (int j = 0; j < LEN_B*ATT; j++) {
            tmp[j] = db[i*LEN_B*ATT + j];
        }
		// sum[i] = agg_variance_sum(tmp, LEN_B, ATT);
        sum[i] = agg_variance_sum(tmp);
	}
	// DT var = sum_tree(sum, LEN_A, 1);
    DT var = sum_tree_a(sum);
	int joined = db[LEN_A*LEN_B * ATT];
	if(joined > 0) {
		return var/joined;
	} else {
		return 0;
	}
}

DT agg_sum_tree(DT *db) {
	DT sum[LEN_B];
	for(int i = 0; i < LEN_B; i++) {
		sum[i] = db[i*ATT+1] + db[i*ATT+2];
	}
	// DT res = sum_tree(sum, LEN_B, 1);
    DT res = sum_tree_b(sum);
	return res;
}

DT agg_mean_decomposed(DT *db) {
	DT tmp[LEN_B*ATT];
	DT sum[LEN_A];
	for(int i = 0; i < LEN_A; i++) {
		// memcpy(tmp, &db[i*LEN_B*att],LEN_B*att*sizeof(DT));
        for (int j = 0; j < LEN_B*ATT; j++) {
            tmp[j] = db[i*LEN_B*ATT+j];
        }
		// sum[i] = agg_sum_tree(tmp, LEN_B, att);
        sum[i] = agg_sum_tree(tmp);
	}
	// DT mean = sum_tree(sum, LEN_A, 1);
    DT mean = sum_tree_a(sum);
	int joined = db[LEN_A*LEN_B*ATT];
	if(joined > 0) {
		return mean/joined;
	} else {
		return 0;
	}
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
	res.joined = cross_join_decomposed(db, INPUT_A.db, INPUT_B.db);
	
	if(res.joined >= LEN_A*LEN_B) { // Limits the last element
			res.joined = LEN_A*LEN_B-1;
	}
	db[LEN_A*LEN_B*ATT] = res.joined;
	// res.analysis1 = agg_mean_decomposed(db, LEN_A*LEN_B, ATT);
    res.analysis1 = agg_mean_decomposed(db);
	// res.analysis2 = agg_variance_decomposed(db, LEN_A*LEN_B, ATT);
    res.analysis2 = agg_variance_decomposed(db);
	//res.analysis2 = variance(db, LEN_A*LEN_B);
	return res;
} 
