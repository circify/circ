int main(__attribute__((private(0))) int a[100], __attribute__((private(1))) int b[100]) { 
    int D = 2;
    int NA = 100;
    int NB = 100;
    int NC = 5;
    int PRECISION = 4;
    int LEN = NA + NB;
    int LEN_OUTER = 10;
    int LEN_INNER = 20;
    

    // init data
    int data[LEN*D];
    for(int i = 0; i < D*NA; i++) {
		data[i]=a[i];
	}
    int offset = NA*D;
    for(int j = 0; j < D*NB; j++) {
		data[i+offset]=b[j];
	}

    int output[D*NC];

    //kmeans
    int c;
    int p;
    int cluster[10]; // NC * D
    for (c = 0; c < 5; c++) {
        cluster[c*D] = data[((c+3)%LEN)*D];
		cluster[c*D+1] = data[((c+3)%LEN)*D+1];
    }

    for (p = 0; p < 4; p++) { 
        int size = NC * D;
		int new_cluster[size]; // NC * D
        int x[size];

		// ======================= iteration_unrolled_outer	
        int count[NC];
        
        // Set Outer result
        for(c = 0; c < NC; c++) {
            new_cluster[c*D] = 0;
            new_cluster[c*D+1] = 0;
            count[c] = 0;
        }	
        
        int loop_clusterD1[NC * LEN_OUTER];
        int loop_clusterD2[NC * LEN_OUTER];
        int loop_count[NC * LEN_OUTER];
        
        // Compute decomposition
        for(j = 0; j < LEN_OUTER; j++) {
            // Copy data, fasthack for scalability
            int data_offset = j*LEN_INNER*D;
            int data_inner[LEN_INNER*D];
            
            // memcpy(data_inner, data+data_offset, LEN_INNER*D*sizeof(coord_t));
            for (i = 0; i < LEN_INNER*D; i++) {
                data_inner[i] = data[i+data_offset];
            }

            int cluster_inner[NC*D];
            int count_inner[NC];
            
            // ======================= iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);
            int dist[NC];
            int pos[NC];
            int bestMap_inner[LEN_INNER];
            
            for(c = 0; c < NC; c++) {
                cluster_inner[c*D] = 0;
                cluster_inner[c*D+1] = 0;
                count_inner[c] = 0;
            }	
            
            // Compute nearest clusters for Data item i
            for(i = 0; i < LEN_INNER; i++) {
                int dx = data_inner[i*D];
                int dy = data_inner[i*D+1];
            
                for(c = 0; c < NC; c++) {
                    pos[c]=c;
                    int x1 = cluster[D*c];
                    int x2 = cluster[D*c+1];
                    int y1 = dx;
                    int y2 = dy;
                    dist[c] = (x1-x2) * (x1-x2) + (y1 - y2) * (y1 - y2);
                }
                bestMap_inner[i] = min_with_aux(dist, pos, NC, 1);

                // hardcoded NC = 5;
                // stride = 1
                // stride = 2
                // stride = 4
                int stride = 1;
                for(i = 0; i + stride < NC; i+=stride<<1) {
                    if(data[i+stride] < data[i]) {
                        data[i] = data[i+stride];
                        aux[i] = aux[i+stride];
                    }
                }
                stride = 2;
                for(i = 0; i + stride < NC; i+=stride<<1) {
                    if(data[i+stride] < data[i]) {
                        data[i] = data[i+stride];
                        aux[i] = aux[i+stride];
                    }
                }
                stride = 4;
                for(i = 0; i + stride < NC; i+=stride<<1) {
                    if(data[i+stride] < data[i]) {
                        data[i] = data[i+stride];
                        aux[i] = aux[i+stride];
                    }
                }
                bestMap_inner[i] = pos[0];
                int cc = bestMap_inner[i];
                cluster_inner[cc*D] += data_inner[i*D];
                cluster_inner[cc*D+1] += data_inner[i*D+1];
                count_inner[cc]++;		
            }
            // ======================= iteration_unrolled_inner_depth(data_inner, cluster, cluster_inner, count_inner, LEN_INNER, NC);


            // Depth: num_cluster Addition
            for(c = 0; c < NC; c++) {
                loop_clusterD1[c * LEN_OUTER + j] = cluster_inner[c*D];
                loop_clusterD2[c * LEN_OUTER + j] = cluster_inner[c*D+1];
                loop_count[c * LEN_OUTER + j] = count_inner[c];
            }
        }

        for(c = 0; c < NC; c++) {
            int tmp = c * LEN_OUTER;

            new_cluster[c*D] = 
                loop_clusterD1[tmp + 0] + loop_clusterD1[tmp + 1] + 
                loop_clusterD1[tmp + 2] + loop_clusterD1[tmp + 3] +
                loop_clusterD1[tmp + 4] + loop_clusterD1[tmp + 5] +
                loop_clusterD1[tmp + 6] + loop_clusterD1[tmp + 7] +
                loop_clusterD1[tmp + 8] + loop_clusterD1[tmp + 9];

            new_cluster[c*D+1] =
                loop_clusterD2[tmp + 0] + loop_clusterD2[tmp + 1] + 
                loop_clusterD2[tmp + 2] + loop_clusterD2[tmp + 3] +
                loop_clusterD2[tmp + 4] + loop_clusterD2[tmp + 5] +
                loop_clusterD2[tmp + 6] + loop_clusterD2[tmp + 7] +
                loop_clusterD2[tmp + 8] + loop_clusterD2[tmp + 9];

            new_cluster[c] = 
                loop_count[tmp + 0] + loop_count[tmp + 1] + 
                loop_count[tmp + 2] + loop_count[tmp + 3] +
                loop_count[tmp + 4] + loop_count[tmp + 5] +
                loop_count[tmp + 6] + loop_count[tmp + 7] +
                loop_count[tmp + 8] + loop_count[tmp + 9];
        }
   

        // Recompute cluster Pos
        // Compute mean
        for(c = 0; c < NC; c++) {  
            if(count[c] >0 ) {
                new_cluster[c*D] /= count[c];
                new_cluster[c*D+1] /= count[c];
            } 
        }


        // ======================= iteration_unrolled_outer
		for(c = 0; c < size; c++) { // NC * D
			cluster[c] = new_cluster[c];
		}
	}

    for(c = 0; c < NC; c++) {  
		output[c*D] = cluster[c*D];
		output[c*D+1] = cluster[c*D+1];
	}

    return 0;
}
