#define D 2 // Dimension (fix)
#define NA 10 // Number of data pounsigneds from Party A
#define NB 10 // Number of data pounsigneds from Party B
#define NC 5 // Number of clusters
#define PRECISION 4

#define LEN (NA+NB)
#define LEN_OUTER 10
#define LEN_INNER (LEN/LEN_OUTER)

struct input_a{
	unsigned dataA[D*NA];
};

struct input_b {
	unsigned dataB[D*NA];
};

struct output {
	unsigned cluster[D*NC];
};


unsigned dist2(unsigned x1, unsigned y1, unsigned x2, unsigned y2) {
  return (x1-x2) * (x1-x2) + (y1 - y2) * (y1 - y2);
}

// Computes minimum in a tree based fashion and associated with aux element
unsigned min_with_aux(unsigned *data, unsigned *aux, unsigned len, unsigned stride) {
	// if(stride > len) {
	// 	return aux[0];
	// } else {
	// 	for(unsigned i = 0; i + stride < len; i+=stride<<1) {
	// 		if(data[i+stride] < data[i]) {
	// 			data[i] = data[i+stride];
	// 			aux[i] = aux[i+stride];
	// 		}
	// 	}
	// 	return min_with_aux(data, aux, len, stride<<1);
	// }
	unsigned min = data[0];
	unsigned res = 0;
	for(unsigned i = 1; i < len; i++){
		if(data[i] < min) {
			min = data[i];
			res = i;
		}
	}
	return res;
}


#define ADD2(X,A)  A[X] + A[X+1u]
#define ADD4(X,A)  ADD2(X,A) + ADD2(X+2u,A)
#define ADD8(X,A)  ADD4(X,A) + ADD4(X+4u,A)
#define ADD10(X,A)  ADD8(X,A) + ADD2(X+8u,A)

/**
 * Iteration loop unrolled and depth minimized by computing minimum over tree structure
 */ 
void iteration_unrolled_inner_depth(unsigned *data_inner, unsigned *cluster, unsigned *OUTPUT_cluster, unsigned *OUTPUT_count, unsigned len_inner, unsigned num_cluster) {
	unsigned i,c;
	unsigned dist[num_cluster];
	unsigned pos[num_cluster];
	unsigned bestMap_inner[len_inner];
	
	for(c = 0u; c < num_cluster; c++) {
		OUTPUT_cluster[c*D] = 0;
		OUTPUT_cluster[c*D+1u] = 0;
		OUTPUT_count[c] = 0;
	}	
	
	// Compute nearest clusters for Data item i
	for(i = 0u; i < len_inner; i++) {
	  unsigned dx = data_inner[i*D];
	  unsigned dy = data_inner[i*D+1];
  
	  for(c = 0u; c < num_cluster; c++) {
			pos[c]=c;
			dist[c] = dist2(cluster[D*c], cluster[D*c+1u], dx, dy);
		}
		bestMap_inner[i] = min_with_aux(dist, pos, num_cluster, 1);
		unsigned cc = bestMap_inner[i];
		OUTPUT_cluster[cc*D] += data_inner[i*D];
		OUTPUT_cluster[cc*D+1u] += data_inner[i*D+1];
		OUTPUT_count[cc]++;		
	}
}

/**
 * Iteration unrolled outer loop
 */ 
void iteration_unrolled_outer(unsigned *data, unsigned *cluster, unsigned *OUTPUT_cluster) {
	// unsigned j, c;
	unsigned j,c;	
	// unsigned count[NC];
	unsigned count[NC];
	
	// Set Outer result
	for(c = 0u; c < NC; c++) {
		OUTPUT_cluster[c*D] = 0;
		OUTPUT_cluster[c*D+1u] = 0;
		count[c] = 0;
	}	
	
	// TODO: loop_clusterD1 -- 2d arrays
	unsigned loop_clusterD1[NC][LEN_OUTER];
	unsigned loop_clusterD2[NC][LEN_OUTER];
	// unsigned loop_count[NC][LEN_OUTER];
	unsigned loop_count[NC][LEN_OUTER];
	
	
	// Compute decomposition
	for(j = 0u; j < LEN_OUTER; j++) {
		// Copy data, fasthack for scalability
		unsigned data_offset = j*LEN_INNER*D;
		unsigned data_inner[LEN_INNER*D];
		
		// memcpy(data_inner, data+data_offset, LEN_INNER*D*sizeof(unsigned));
		for (unsigned i = 0; i < LEN_INNER * D; i++)
		{
			data_inner[i] = data[i + data_offset];
		}

		unsigned cluster_inner[NC*D];
		// unsigned count_inner[NC];
		unsigned count_inner[NC];
		
		iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);

		// Depth: num_cluster Addition
		for(c = 0u; c < NC; c++) {
			loop_clusterD1[c][j] = cluster_inner[c*D];
			loop_clusterD2[c][j] = cluster_inner[c*D+1u];
			loop_count[c][j] = count_inner[c];
		}
	}
	
	for(c = 0u; c < NC; c++) {
		OUTPUT_cluster[c*D] = ADD10(0,loop_clusterD1[c]);
		OUTPUT_cluster[c*D+1u] = ADD10(0,loop_clusterD2[c]);
		count[c] = ADD10(0, loop_count[c]);
	}	

	// Recompute cluster Pos
	// Compute mean
	for(c = 0u; c < NC; c++) {  
	  if(count[c] > 0) {
			OUTPUT_cluster[c*D] /= count[c];
			OUTPUT_cluster[c*D+1u] /= count[c];
	  } 
	}
}



void kmeans(unsigned *data, unsigned *OUTPUT_res) {
	// unsigned c, p;
	unsigned c, p;
	unsigned cluster[NC*D];

	// Assign random start cluster from data
	for(c = 0u; c < NC; c++) {
		cluster[c*D] = data[((c+3u)%LEN)*D];
		cluster[c*D+1u] = data[((c+3u)%LEN)*D+1u];
	}

	for (p = 0u; p < PRECISION; p++) { 
		unsigned new_cluster[NC*D];
		iteration_unrolled_outer(data, cluster, new_cluster);
		// iteration(data, cluster, new_cluster, len, num_cluster);
		
		// We need to copy inputs to outputs
		for(c = 0u; c < NC*D; c++) {
			cluster[c] = new_cluster[c];
		}
	}

	for(c = 0u; c < NC; c++) {  
		OUTPUT_res[c*D] = cluster[c*D];
		OUTPUT_res[c*D+1u] = cluster[c*D+1u];
	}
}


unsigned main(__attribute__((private(0))) unsigned a[20], __attribute__((private(1))) unsigned b[20])
{
    // init data
    unsigned data[LEN * D];
    for (unsigned i = 0; i < D * NA; i++)
    {
        data[i] = a[i];
    }
    unsigned offset = D * NA;
    for (unsigned i = 0; i < D * NB; i++)
    {
        data[i + offset] = b[i];
    }

    struct output output;
    kmeans(data, output.cluster);
   
    unsigned sum = 0;
    for (unsigned i = 0; i < D * NC; i++)
    {
        sum += output.cluster[i];
    }
    return sum;
}
