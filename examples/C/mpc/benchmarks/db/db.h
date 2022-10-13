/**
 * Example on how to merge two data sets and to perform various analyses
 */

#define LEN (LEN_A + LEN_B)
#define ATT (ATT_A + ATT_B - 1) // Number of joined attributes
 
typedef int DT;

typedef struct
{
	DT db[LEN_A*ATT_A];
} InputA;


typedef struct
{
	DT db[LEN_B*ATT_B];
} InputB;

typedef struct
{
	DT analysis1;
	DT analysis2;
	int joined;
} Output;


// Stride start = 1
// DT sum_tree(DT *data, int len, int stride) {
// 	if(stride > len) {
// 		return data[0];
// 	} else {
// 		for(int i = 0; i + stride < len; i+=stride<<1) {
// 			data[i]+=data[i+stride];
// 		}
// 		return sum_tree(data, len, stride<<1);
// 	}
// }

DT sum_tree(DT *data, int len, int stride) {
	int sum = 0;
	for (int i = 0; i < len; i++) {
		sum += data[i];
	}
	return sum;
}

// Counts how many non-zero values are in an array
DT sum_gt_zero(DT *data, int len) {
	DT tmp[len>>1];
	for(int i = 0; i + 1 < len; i+=2) {
		tmp[i>>1] = (data[i]>0) + (data[i+1]>0);
	}
	return sum_tree(tmp, len>>1, 1);
}

/*DT mean_with_abort_tree(DT *data, int len) {
	DT mean = sum_tree(data, len, 1);
	
	return mean;
}*/


DT mean_with_abort(DT *db, unsigned len) {
	DT mean = 0;
	int i;
	for(i = 0; i < len && db[i] >= 0; i++) {
		mean += db[i];
	}
	if(i > 0) {
		return mean/i;
	} else {
		return 0;
	}
}


DT mean(DT *db, unsigned len) {
	//DT mean = 0;
	/*for(int i = 0; i < len; i++) {
		mean += db[i];
	}*/
	DT mean = sum_tree(db, len, 1);
	return mean/len;
}

DT variance(DT *db, unsigned len) {
	DT exp = mean(db, len);
	DT var[len];// = 0;
	for(int i = 0; i < len; i++) {
		DT dist = db[i] - exp;
		var[i] = dist * dist;
		//var += dist;
	}
	DT res = sum_tree(var, len, 1);
	return res / len;
}
