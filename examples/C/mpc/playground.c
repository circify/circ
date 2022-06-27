// int fa(int *data, int* res) {
// 	return res[1];
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
// 	int data[2] = {2,3};
// 	int res[2] = {6,7};
// 	int t = fa(data, res);
// 	return t;
// }


// int fa(int * t) {
// 	t[0] += 1;
// 	return t[0] + 1;
// }	


// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
//     int data[1] = {0};
// 	for (int i = 0; i < 2; i++) {
// 		data[0] += fa(data);
// 	}
// 	return data[0];
// }


#define D 2 // Dimension (fix)
#define NA 10 // Number of data points from Party A
#define NB 10 // Number of data points from Party B
#define NC 5 // Number of clusters
#define PRECISION 4

#define LEN (NA+NB)
#define LEN_OUTER 10
#define LEN_INNER (LEN/LEN_OUTER)


int dist2(int x1, int y1, int x2, int y2) {
  return (x1-x2) * (x1-x2) + (y1 - y2) * (y1 - y2);
}

// Computes minimum in a tree based fashion and associated with aux element
int min_with_aux(int *data, int *aux, int len, int stride) {
	int min = data[0];
	int res = 0;
	for(int i = 1; i < NC; i++){
		if(data[i] < min) {
			min = data[i];
			res = i;
		}
	}
	return res;
}


/**
 * Iteration loop unrolled and depth minimized by computing minimum over tree structure
 */ 
void iteration_unrolled_inner_depth(int *data_inner, int *cluster, int *OUTPUT_cluster, int *OUTPUT_count, int len_inner, int num_cluster) {
	int i,c;
	int dist[NC];
	int pos[NC];
	int bestMap_inner[LEN_INNER];
	
	for(c = 0; c < NC; c++) {
		OUTPUT_cluster[c*D] = 0;
		OUTPUT_cluster[c*D+1] = 0;
		OUTPUT_count[c] = 0;
	}	
	
	// Compute nearest clusters for Data item i
	for(i = 0; i < LEN_INNER; i++) {
        int dx = data_inner[i*D];
        int dy = data_inner[i*D+1];

        for(c = 0; c < NC; c++) {
            pos[c]=c;
            dist[c] = dist2(cluster[D*c], cluster[D*c+1], dx, dy);
        }        
		bestMap_inner[i] = min_with_aux(dist, pos, num_cluster, 1);
        int cc = bestMap_inner[i];
        OUTPUT_cluster[cc*D] += data_inner[i*D];
        OUTPUT_cluster[cc*D+1] += data_inner[i*D+1];
        OUTPUT_count[cc]++;
	}
}

#define ADD2(X,A)  A[X] + A[X+1]
#define ADD4(X,A)  ADD2(X,A) + ADD2(X+2,A)
#define ADD8(X,A)  ADD4(X,A) + ADD4(X+4,A)
#define ADD10(X,A)  ADD8(X,A) + ADD2(X+8,A)

/**
 * Iteration unrolled outer loop
 */ 
void iteration_unrolled_outer(int *data, int *cluster, int *OUTPUT_cluster) {
	int j, c;
	int count[NC];
	
	// Set Outer result
	for(c = 0; c < NC; c++) {
		OUTPUT_cluster[c*D] = 0;
		OUTPUT_cluster[c*D+1] = 0;
		count[c] = 0;
	}	
	
	// TODO: loop_clusterD1 -- 2d arrays
	int loop_clusterD1[NC][LEN_OUTER];
	int loop_clusterD2[NC][LEN_OUTER];
	// int loop_count[NC][LEN_OUTER];
	int loop_count[NC][LEN_OUTER];
	
	
	// Compute decomposition
	for(j = 0; j < LEN_OUTER; j++) {
		// Copy data, fasthack for scalability
		int data_offset = j*LEN_INNER*D;
		int data_inner[LEN_INNER*D];
		
		// memcpy(data_inner, data+data_offset, LEN_INNER*D*sizeof(int));
		for (int i = 0; i < LEN_INNER * D; i++)
		{
			data_inner[i] = data[i + data_offset];
		}

		int cluster_inner[NC*D] = {0,0,0,0,0,0,0,0,0,0};
		// int count_inner[NC];
		int count_inner[NC] = {0,0,0,0,0};
		
		iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);

		// Depth: num_cluster Addition
		for(c = 0; c < NC; c++) {
			loop_clusterD1[c][j] = cluster_inner[c*D];
			loop_clusterD2[c][j] = cluster_inner[c*D+1];
			loop_count[c][j] = count_inner[c];
		}
	}
	
	for(c = 0; c < NC; c++) {
		OUTPUT_cluster[c*D] = ADD10(0,loop_clusterD1[c]);
		OUTPUT_cluster[c*D+1] = ADD10(0,loop_clusterD2[c]);
		count[c] = ADD10(0, loop_count[c]);
	}	

	// Recompute cluster Pos
	// Compute mean
	for(c = 0; c < NC; c++) {  
	  if(count[c] > 0) {
			OUTPUT_cluster[c*D] /= count[c];
			OUTPUT_cluster[c*D+1] /= count[c];
	  } 
	}
}


int kmeans(int *data, int *OUTPUT_res) {
	// int c, p;
	int c, p;
	int cluster[NC*D];
	int new_cluster[NC*D];
    for (int i = 0; i < NC * D; i++) {
        cluster[i] = 0;
    }

	// Assign random start cluster from data
	for(c = 0; c < NC; c++) {
		cluster[c*D] = data[((c+3)%LEN)*D];
		cluster[c*D+1] = data[((c+3)%LEN)*D+1];
	}

	for (p = 0; p < PRECISION; p++) { 
        for (int i = 0; i < NC * D; i++) {
            new_cluster[i] = 0;
        }

		iteration_unrolled_outer(data, cluster, new_cluster);
		// iteration(data, cluster, new_cluster, len, num_cluster);
		
		// We need to copy inputs to outputs
		for( c = 0; c < NC*D; c++) {
			cluster[c] = new_cluster[c];
		}
	}

	for(c = 0; c < NC; c++) {  
		OUTPUT_res[c*D] = cluster[c*D];
		OUTPUT_res[c*D+1] = cluster[c*D+1];
	}
}

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
	// int data[LEN * D];
	// for (int i = 0; i < LEN * D; i++) {
	// 	data[i] = i;
	// }

	// int cluster[NC*D] = {0,0,0,0,0,0,0,0,0,0};
	// int new_cluster[NC*D] = {0,0,0,0,0,0,0,0,0,0};

	// iteration_unrolled_outer(data, cluster, new_cluster);
	// // return cluster[0];
	// return data[2];

	int data[LEN * D];
	for (int i = 0; i < LEN * D; i++) {
		data[i] = i;
	}
	int OUTPUT_cluster[NC*D] = {0,0,0,0,0,0,0,0,0,0};
	kmeans(data, OUTPUT_cluster);
	return OUTPUT_cluster[1];
}


// #define NC 1
// #define LEN_INNER 1
// #define D 1 

// int dist2(int x1, int y1, int x2, int y2) {
//   return (x1-x2) * (x1-x2) + (y1 - y2) * (y1 - y2);
// }

// void iteration_unrolled_inner_depth(int *data_inner, int *cluster, int *OUTPUT_cluster, int *OUTPUT_count) {
// 	int i,c;
// 	int dist[NC];
// 	int pos[NC];
// 	int bestMap_inner[LEN_INNER];
	
// 	for(c = 0; c < NC; c++) {
// 		OUTPUT_cluster[c*D] = 0;
// 		OUTPUT_cluster[c*D+1] = 0;
// 		OUTPUT_count[c] = 0;
// 	}	
	
// 	// Compute nearest clusters for Data item i
// 	for(i = 0; i < LEN_INNER; i++) {
// 		int dx = 0;
// 		int dy = 0;
// 		OUTPUT_cluster[0] += dist2(cluster[0], cluster[1], dx, dy);
// 	}
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
//     int data_inner[1] = {0};
//     int cluster[2] = {0, 0};
//     int OUTPUT_cluster[2] = {0, 0};
//     int OUTPUT_count[1] = {0};

//     iteration_unrolled_inner_depth(data_inner, cluster, OUTPUT_cluster, OUTPUT_count);

// }


// #define LEN 1

// int fa(int * c, int a) {
//     for (int i = 0; i < LEN; i++) {
//         c[i] = c[i] + a;
//     }
//     return 1;
// }

// int dist(int a, int b, int c, int d) {
//     return a + b + c + d + 1;
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
//     int c[LEN];
//     int res[LEN];
//     res[0] += dist(c[0], c[0], c[0], c[0]);
//     int sum = res[0];
//     for (int i = 0; i < LEN; i++) {
//         sum += c[i];
//     }
//     return sum;
// }

// #define LEN 1

// int fa(int * c, int a) {
//     for (int i = 0; i < LEN; i++) {
//         c[i] = c[i] + a;
//     }
//     return 1;
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
//     int c[LEN];
//     int ret = fa(c, a);
//     int sum = ret;
//     for (int i = 0; i < LEN; i++) {
//         sum += c[i];
//     }
//     return sum;
// }

// int fa(int a, int b, int c) {
//     return a + b + c + 1;
// }

// int fb(int a) {
//     return fa(a, a, a);
// }

// int fc(int a) {
//     return fb(a);
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
//     int c = fc(a) + fc(b); 
//     return c;
// }