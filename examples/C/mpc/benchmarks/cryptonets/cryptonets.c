// Parameters taken from the paper
#define IMAGE_WIDTH 28 // 28
#define WINDOW_WIDTH 5
#define STRIDE 2
#define OUTPUT_CHANNELS 5 // 5

#define IMAGE_CROP 13 // 13 with padding
#define SIZE_CONVOLUTION (IMAGE_CROP * IMAGE_CROP) // 169

#define FULLY_CONNECTED_WIDTH 100 // (7, 9)
#define FINAL_OUTPUT_CHANNELS 10

typedef int DT;

DT relu(DT val) {
	if(val>0) {
		return val;
	} else {
		return 0;
	}
}


DT activate_sqr(DT val) {
	DT res = val*val;
	return res;
}

void max_pooling(DT *vals, DT *OUTPUT_res, int cols, int rows) {
	int rows_res = rows / 2;
	int cols_res = cols / 2;
	for(int i = 0; i < rows_res; i++) {
		for(int j = 0; j < cols_res; j++) {
			int x = j * 2;
			int y = i * 2;
			DT max = vals[y*cols + x];
			if(vals[y*cols + x + 1] > max) {
				max = vals[y*cols + x + 1];
			}
			if(vals[(y + 1) *cols + x] > max) {
				max = vals[(y + 1) * cols + x];
			} 
			if(vals[(y + 1) *cols + x + 1] > max) {
				max = vals[(y + 1) * cols + x + 1];
			} 
			OUTPUT_res[i * cols_res + j] = max;
		}
	}
}

void max_pooling_outputs(DT *vals, DT *OUTPUT_res, int outputs, int cols, int rows) {
	for(int o = 0; o < outputs; o++) {
		int size = cols*rows; 
		DT input_layer[size]; // We copy data, because compiler is unable to slice array efficiently
		for(int i = 0; i < size; i++) {
			input_layer[i] = vals[o*size+i];
		}
		int output_size = cols/2*rows/2;
		DT res_layer[output_size];
		max_pooling(input_layer, res_layer, cols, rows);
		for(int i = 0; i < output_size; i++) {
			OUTPUT_res[o*output_size+i] = res_layer[i];
		}
	}
}

DT mmulT_unrolled_inner(DT* a, DT* b, int common) { 
	DT sum = 0;
	
	int i = 0;
	// Add the first as groups of eight
	while(i+8<= common) {
		sum += a[i+0]*b[i+0] + a[i+1]*b[i+1] + a[i+2]*b[i+2] + a[i+3]*b[i+3] + a[i+4]*b[i+4] + a[i+5]*b[i+5] + a[i+6]*b[i+6] + a[i+7]*b[i+7];
		i+=8;
	}
	if(i+4<=common) {
		sum += a[i+0]*b[i+0] + a[i+1]*b[i+1] + a[i+2]*b[i+2] + a[i+3]*b[i+3];
		i+=4;
	}
	for(i; i < common; i++) {
		sum += a[i] * b[i];
	}
	
	/*for(int k = 0; k < common; k++) {
		sum += a[k] * b[k];
	}*/
	return sum;
}


void mmulT_unrolled(DT* a, DT* b, DT *OUTPUT_res, int cols_a, int cols_b, int common) {
	for(int i = 0; i < cols_a; i++) {
		DT aRow[common];
		// memcpy(aRow, a+i*common, common*sizeof(DT));
        for (int k = 0; k < common; k++) {
            aRow[k] = (a+i*common)[k];
        }

		for(int j = 0; j < cols_b; j++) {
			DT bRow[common];
			// memcpy(bRow, b+j*common, common*sizeof(DT));
            for (int k = 0; k < common; k++) {
                bRow[k] = (b+j*common)[k];
            }
			OUTPUT_res[i*cols_b+j] = mmulT_unrolled_inner(aRow, bRow,common);
		}
	}
}


void convolution_naive(DT *image, DT* kernel, DT* OUTPUT_layer, int image_width, int window_size, int stride, int conv_width)
{
	int window_unrolled = window_size * window_size;
	// Need to assign each input pixel to the convolution matrix
	int x, y, wx=0, wy;
	for(y = 0; y < conv_width; y++) { // Inner position in the image
		for(x = 0; x < conv_width; x++) {
			int oPos = x+y*conv_width;
			DT tmp = 0;
			for(wy = 0; wy < window_size; wy++) {
                int convPos = wx+wy*window_size;
                tmp += kernel[convPos] * image[(y*stride + wy) * image_width + (x*stride + 0)] + kernel[convPos] * image[(y*stride + wy) * image_width + (x*stride + 1)] + kernel[convPos] * image[(y*stride + wy) * image_width + (x*stride + 2)] + kernel[convPos] * image[(y*stride + wy) * image_width + (x*stride + 3)] + kernel[convPos] * image[(y*stride + wy) * image_width + (x*stride + 4)];
			}
			OUTPUT_layer[oPos] = tmp;
		}
	}
}

void convolution_naive_outputs(DT *image, DT* kernels, DT* OUTPUT_layer, int image_width, int window_size, int output_size, int stride, int conv_width) {	
	//int res[conv_width*conv_width*];
	int kernel_size = window_size*window_size;
	for(int o = 0; o < output_size; o++) {
		DT kernel[kernel_size];
		DT res[conv_width*conv_width];
		// memcpy(kernel, kernels+o*kernel_size, kernel_size* sizeof(DT));
        for (int k = 0; k < kernel_size; k++) {
            kernel[k] = (kernels+o*kernel_size)[k];
        }
		convolution_naive(image, kernel, res, image_width, window_size, stride, conv_width);
		// memcpy(OUTPUT_layer + o*(conv_width*conv_width), res, conv_width*conv_width * sizeof(DT));
        for (int k = 0; k < conv_width*conv_width; k++) {
            (OUTPUT_layer + o*(conv_width*conv_width))[k] = res[k];
        }
	}
}

typedef struct 
{
	DT image[IMAGE_WIDTH * IMAGE_WIDTH];
} InputA;


typedef struct
{
	DT kernelsL1[OUTPUT_CHANNELS * WINDOW_WIDTH * WINDOW_WIDTH]; // (1)
	DT pool_layer[FULLY_CONNECTED_WIDTH * SIZE_CONVOLUTION * OUTPUT_CHANNELS];
	DT fc[FINAL_OUTPUT_CHANNELS * FULLY_CONNECTED_WIDTH];
} InputB;

typedef struct
{
	DT final_layer[FINAL_OUTPUT_CHANNELS];
} Output;

DT mmulT_unrolled_inner_1(DT* a, DT* b) { 
	DT sum = 0;
	
	int i = 0;
	// Add the first as groups of eight
	for (i=0; i+8< OUTPUT_CHANNELS * SIZE_CONVOLUTION; i+=8) {
		sum += a[i+0]*b[i+0] + a[i+1]*b[i+1] + a[i+2]*b[i+2] + a[i+3]*b[i+3] + a[i+4]*b[i+4] + a[i+5]*b[i+5] + a[i+6]*b[i+6] + a[i+7]*b[i+7];
	}
	if(i+4<OUTPUT_CHANNELS * SIZE_CONVOLUTION) {
		sum += a[i+0]*b[i+0] + a[i+1]*b[i+1] + a[i+2]*b[i+2] + a[i+3]*b[i+3];
		i+=4;
	}
	for(i=0; i < OUTPUT_CHANNELS * SIZE_CONVOLUTION; i++) {
		sum += a[i] * b[i];
	}
	
	/*for(int k = 0; k < common; k++) {
		sum += a[k] * b[k];
	}*/
	return sum;
}


void mmulT_unrolled_1(DT* a, DT* b, DT *OUTPUT_res) {
	for(int i = 0; i < FULLY_CONNECTED_WIDTH; i++) {
		DT aRow[OUTPUT_CHANNELS * SIZE_CONVOLUTION];
		// memcpy(aRow, a+i*common, common*sizeof(DT));
        for (int k = 0; k < OUTPUT_CHANNELS * SIZE_CONVOLUTION; k++) {
            aRow[k] = (a+i*OUTPUT_CHANNELS * SIZE_CONVOLUTION)[k];
        }

		for(int j = 0; j < 1; j++) {
			DT bRow[OUTPUT_CHANNELS * SIZE_CONVOLUTION];
			// memcpy(bRow, b+j*common, common*sizeof(DT));
            for (int k = 0; k < OUTPUT_CHANNELS * SIZE_CONVOLUTION; k++) {
                bRow[k] = (b+j*OUTPUT_CHANNELS * SIZE_CONVOLUTION)[k];
            }
			OUTPUT_res[i*1+j] = mmulT_unrolled_inner_1(aRow, bRow);
		}
	}
}


void convolution_naive_1(DT *image, DT* kernel, DT* OUTPUT_layer)
{
	int window_unrolled = WINDOW_WIDTH * WINDOW_WIDTH;
	// Need to assign each input pixel to the convolution matrix
	int x, y, wx=0, wy;
	for(y = 0; y < IMAGE_CROP; y++) { // Inner position in the image
		for(x = 0; x < IMAGE_CROP; x++) {
			int oPos = x+y*IMAGE_CROP;
			DT tmp = 0;
			for(wy = 0; wy < WINDOW_WIDTH; wy++) {
                int convPos = wx+wy*WINDOW_WIDTH;
                tmp += kernel[convPos] * image[(y*STRIDE + wy) * (IMAGE_WIDTH+2) + (x*STRIDE + 0)] + kernel[convPos] * image[(y*STRIDE + wy) * (IMAGE_WIDTH+2) + (x*STRIDE + 1)] + kernel[convPos] * image[(y*STRIDE + wy) * (IMAGE_WIDTH+2) + (x*STRIDE + 2)] + kernel[convPos] * image[(y*STRIDE + wy) * (IMAGE_WIDTH+2) + (x*STRIDE + 3)] + kernel[convPos] * image[(y*STRIDE + wy) * (IMAGE_WIDTH+2) + (x*STRIDE + 4)];
			}
			OUTPUT_layer[oPos] = tmp;
		}
	}
}

void convolution_naive_outputs_1(DT *image, DT* kernels, DT* OUTPUT_layer) {	
	//int res[conv_width*conv_width*];
	int kernel_size = WINDOW_WIDTH*WINDOW_WIDTH;
	for(int o = 0; o < OUTPUT_CHANNELS; o++) {
		DT kernel[kernel_size];
		DT res[IMAGE_CROP*IMAGE_CROP];
		// memcpy(kernel, kernels+o*kernel_size, kernel_size* sizeof(DT));
        for (int k = 0; k < kernel_size; k++) {
            kernel[k] = (kernels+o*kernel_size)[k];
        }
		// convolution_naive(image, kernel, res, IMAGE_WIDTH+2, WINDOW_WIDTH, STRIDE, IMAGE_CROP);
        convolution_naive_1(image, kernel, res);                 
		// memcpy(OUTPUT_layer + o*(conv_width*conv_width), res, conv_width*conv_width * sizeof(DT));
        for (int k = 0; k < IMAGE_CROP*IMAGE_CROP; k++) {
            (OUTPUT_layer + o*(IMAGE_CROP*IMAGE_CROP))[k] = res[k];
        }
	}
}


int main(__attribute__((private(0))) InputA INPUT_A, __attribute__((private(1))) InputB INPUT_B)
{
	Output OUTPUT_classify;		
	
	// Two lines of padding 
	int padded_width = IMAGE_WIDTH+2;
	DT convolution_input[padded_width*padded_width];
	for(int i = 0; i < padded_width; i++) {
		convolution_input[i] = 0;
		convolution_input[i+padded_width] = 0;
		convolution_input[padded_width*i] = 0;
		convolution_input[padded_width*i+1] = 0;
	} 
	for(int y = 0; y < IMAGE_WIDTH; y++) {
		for(int x = 0; x < IMAGE_WIDTH; x++) {
			convolution_input[(y+2)*padded_width+(x+2)] = INPUT_A.image[y*IMAGE_WIDTH+x];
		}
	}

	// Convolution (1)
	DT convolution_layer[OUTPUT_CHANNELS * SIZE_CONVOLUTION];
	convolution_naive_outputs_1(convolution_input, INPUT_B.kernelsL1, convolution_layer);
	
	
	// Activation Function (2)
	for(int i = 0; i < OUTPUT_CHANNELS * SIZE_CONVOLUTION; i++) {
		convolution_layer[i] = activate_sqr(convolution_layer[i]);
	}
	
	// Combination of Mean pooling and Fully connected (3)
	DT im_layer[FULLY_CONNECTED_WIDTH];	
	// mmulT_unrolled(INPUT_B.pool_layer, convolution_layer, im_layer, FULLY_CONNECTED_WIDTH, 1, OUTPUT_CHANNELS * SIZE_CONVOLUTION);
    mmulT_unrolled_1(INPUT_B.pool_layer, convolution_layer, im_layer);


	// // Activation Function (4)
	// for(int i = 0; i < FULLY_CONNECTED_WIDTH; i++) {
	// 	im_layer[i] = activate_sqr(im_layer[i]);
	// }

	// // Fully Connected (5)
	// DT final_layer[FINAL_OUTPUT_CHANNELS];
	// mmulT_unrolled(INPUT_B.fc, im_layer, final_layer, FINAL_OUTPUT_CHANNELS, 1, FULLY_CONNECTED_WIDTH);
	
	// for(int i = 0; i < FINAL_OUTPUT_CHANNELS; i++) {
	// 	OUTPUT_classify.final_layer[i] = final_layer[i];
	// }

    int sum = 0;
	for (int i = 0; i < FINAL_OUTPUT_CHANNELS; i++) {
		sum += OUTPUT_classify.final_layer[i];
	}

	// return OUTPUT_classify;
    return sum;
}

