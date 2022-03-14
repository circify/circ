int D = 2;
int NA = 10;
int NB = 10;
int NC = 5;
int PRECISION = 4;
int LEN = NA + NB;
int LEN_OUTER = 10;
int LEN_INNER = LEN / LEN_OUTER;

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

int add2(int X, int* A) {
	return A[X] + A[X+1];
}

int add4(int X, int* A) {
	return add2(X,A) + add2(X+2,A);
}

int add8(int X, int* A) {
	return add4(X,A) + add4(X+4,A);
}

int add10(int X, int* A) {
	return add8(X,A) + add2(X+8,A);
}

/**
 * Iteration unrolled outer loop
 */ 
void iteration_unrolled_outer(int *data, int *cluster, int *OUTPUT_cluster) {
	// unsigned j, c;
	int j,c;	
	// unsigned count[NC];
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
	// unsigned loop_count[NC][LEN_OUTER];
	int loop_count[NC][LEN_OUTER];
	
	
	// Compute decomposition
	for(j = 0; j < LEN_OUTER; j++) {
		// Copy data, fasthack for scalability
		int data_offset = j*LEN_INNER*D;
		int data_inner[LEN_INNER*D];
		
		// memcpy(data_inner, data+data_offset, LEN_INNER*D*sizeof(coord_t));
		for (int i_6 = 0; i_6 < LEN_INNER * D; i_6++)
		{
			data_inner[i_6] = data[i_6 + data_offset];
		}

		int cluster_inner[NC*D];
		// unsigned count_inner[NC];
		int count_inner[NC];
		
		// iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);

		// // Depth: num_cluster Addition
		for(c = 0; c < NC; c++) {
			// loop_clusterD1[c][j] = cluster_inner[c*D];
			// loop_clusterD2[c][j] = cluster_inner[c*D+1];
			// loop_count[c][j] = count_inner[c];
		}
	}
	
	for(c = 0; c < NC; c++) {
		// TODO: loop_clusterD1 -- 2d arrays
		// OUTPUT_cluster[c*D] = add10(0,loop_clusterD1[c]);
		// OUTPUT_cluster[c*D+1] = add10(0,loop_clusterD2[c]);
		// count[c] = add10(0, loop_count[c]);
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
	// unsigned c, p;
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
	// 	// iteration(data, cluster, new_cluster, len, num_cluster);
		
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
