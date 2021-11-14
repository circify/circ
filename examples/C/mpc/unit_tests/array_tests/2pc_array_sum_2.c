int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) { 
    //nested for loop test
    int acc = 0;
    int D = 2;
    int NC = 5;



    int output[D*NC];

    // ======================= kmeans
    int cluster[D*NC];

    // Assign random start cluster from data
    for (int i_2 = 0; i_2 < NC; i_2++) {
        cluster[i_2*D] = data[((i_2+3)%LEN)*D];
		cluster[i_2*D+1] = data[((i_2+3)%LEN)*D+1];
    }


    for(int i_17 = 0; i_17 < NC; i_17++) {  
		output[i_17*D] = cluster[i_17*D];
		output[i_17*D+1] = cluster[i_17*D+1];
	}



    return acc;
}