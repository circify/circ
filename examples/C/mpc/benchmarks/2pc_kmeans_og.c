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

void kmeans(int *data, int *OUTPUT_res) {
	unsigned c, p;
	int cluster[NC*D];

	// Assign random start cluster from data
	for(c = 0; c < NC; c++) {
		cluster[c*D] = data[((c+3)%LEN)*D];
		cluster[c*D+1] = data[((c+3)%LEN)*D+1];
	}

	for (p = 0; p < PRECISION; p++) { 
		int new_cluster[NC*D];
		// iteration_unrolled_outer(data, cluster, new_cluster);
		//iteration(data, cluster, new_cluster, len, num_cluster);
		
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
