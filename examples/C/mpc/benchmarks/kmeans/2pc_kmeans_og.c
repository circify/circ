#define D 2 // Dimension (fix)
#define NA 10 // Number of data points from Party A
#define NB 10 // Number of data points from Party B
#define NC 5 // Number of clusters
#define PRECISION 4

#define LEN (NA+NB)
#define LEN_OUTER 10
#define LEN_INNER (LEN/LEN_OUTER)

struct input_a{
	int dataA[D*NA];
};

struct input_b {
	int dataB[D*NA];
};

struct output {
	int cluster[D*NC];
};


int dist2(int x1, int y1, int x2, int y2) {
  return (x1-x2) * (x1-x2) + (y1 - y2) * (y1 - y2);
}

// Computes minimum in a tree based fashion and associated with aux element
int min_with_aux(int *data, int *aux, int len, int stride) {
	// if(stride > len) {
	// 	return aux[0];
	// } else {
	// 	for(int i = 0; i + stride < len; i+=stride<<1) {
	// 		if(data[i+stride] < data[i]) {
	// 			data[i] = data[i+stride];
	// 			aux[i] = aux[i+stride];
	// 		}
	// 	}
	// 	return min_with_aux(data, aux, len, stride<<1);
	// }
	int min = data[0];
	int res = 0;
	for(int i = 1; i < len; i++){
		if(data[i] < min) {
			min = data[i];
			res = i;
		}
	}
	return res;
}


#define ADD2(X,A)  A[X] + A[X+1]
#define ADD4(X,A)  ADD2(X,A) + ADD2(X+2,A)
#define ADD8(X,A)  ADD4(X,A) + ADD4(X+4,A)
#define ADD10(X,A)  ADD8(X,A) + ADD2(X+8,A)

/**
 * Iteration loop unrolled and depth minimized by computing minimum over tree structure
 */ 
void iteration_unrolled_inner_depth(int *data_inner, int *cluster, int *OUTPUT_cluster, int *OUTPUT_count, int len_inner, int num_cluster) {
	int i,c;
	int dist[num_cluster];
	int pos[num_cluster];
	int bestMap_inner[len_inner];
	
	for(c = 0; c < num_cluster; c++) {
		OUTPUT_cluster[c*D] = 0;
		OUTPUT_cluster[c*D+1] = 0;
		OUTPUT_count[c] = 0;
	}	
	
	// Compute nearest clusters for Data item i
	for(i = 0; i < len_inner; i++) {
	  int dx = data_inner[i*D];
	  int dy = data_inner[i*D+1];
  
	  for(c = 0; c < num_cluster; c++) {
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

/**
 * Iteration unrolled outer loop
 */ 
void iteration_unrolled_outer(int *data, int *cluster, int *OUTPUT_cluster) {
	// int j, c;
	int j,c;	
	// int count[NC];
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

		int cluster_inner[NC*D];
		// int count_inner[NC];
		int count_inner[NC];
		
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
	  if(count[c] >0 ) {
			OUTPUT_cluster[c*D] /= count[c];
			OUTPUT_cluster[c*D+1] /= count[c];
	  } 
	}
}



void kmeans(int *data, int *OUTPUT_res) {
	// int c, p;
	int c, p;
	int cluster[NC*D];

	// Assign random start cluster from data
	for(c = 0; c < NC; c++) {
		cluster[c*D] = data[((c+3)%LEN)*D];
		cluster[c*D+1] = data[((c+3)%LEN)*D+1];
	}

	for (p = 0; p < PRECISION; p++) { 
		int new_cluster[NC*D];
		iteration_unrolled_outer(data, cluster, new_cluster);
		// iteration(data, cluster, new_cluster, len, num_cluster);
		
		// We need to copy inputs to outputs
		for(c = 0; c < NC*D; c++) {
			cluster[c] = new_cluster[c];
		}
	}

	for(c = 0; c < NC; c++) {  
		OUTPUT_res[c*D] = cluster[c*D];
		OUTPUT_res[c*D+1] = cluster[c*D+1];
	}
}


int main(__attribute__((private(0))) int a[20], __attribute__((private(1))) int b[20])
{
    // init data
    int data[LEN * D];
    for (int i = 0; i < D * NA; i++)
    {
        data[i] = a[i];
    }
    int offset = D * NA;
    for (int i = 0; i < D * NB; i++)
    {
        data[i + offset] = b[i];
    }

    struct output output;
    kmeans(data, output.cluster);
   
    int sum = 0;
    for (int i = 0; i < D * NC; i++)
    {
        sum += output.cluster[i];
    }
    return sum;
}
