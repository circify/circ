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
    int data[400];
    for(int i = 0; i < D*NA; i++) {
		data[i]=a[i];
	}
    for(int j = 0; j < D*NB; j++) {
		data[j+200]=b[j];
	}

    //kmeans
    int cluster[10]; // NC * D
    for (int c0 = 0; c0 < 5; c0++) {
        cluster[c0*D] = data[((c0+3)%LEN)*D];
		cluster[c0*D+1] = data[((c0+3)%LEN)*D+1];
    }

    for (int p = 0; p < 4; p++) { 
        int size = NC * D;
		int new_cluster[size]; // NC * D
        int x[size];
		// iteration_unrolled_outer(data, cluster, new_cluster);
		
		for(int c1 = 0; c1 < size; c1++) { // NC * D
			cluster[c1] = new_cluster[c1];
		}
	}

    return 0;
}
