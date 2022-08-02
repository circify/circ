typedef int DT;

void memcpy(int* destination, int* source, int size) {
	for (int i = 0; i < size; i++) {
		destination[i] = source[i];
	}
}

void DT_memset(DT* OUTPUT_res, int len, DT val) {
	for(int i = 0; i < len; i++) {
		OUTPUT_res[i] = val;
	}
}

DT relu(DT val) {
	if(val>0) {
		return val;
	} else {
		return 0;
	}
}
void relu_map(DT *in, DT *OUTPUT_res, int len) {
	for(int i = 0; i < len; i++) {
		OUTPUT_res[i] = relu(in[i]);
	}
}

void decomposed_relu(DT *in, DT *OUTPUT_res, int len_outer, int len_inner) {
	DT copy[len_inner];
	DT im_res[len_inner];
	for(int i = 0; i < len_outer; i++) {
		// memcpy(copy, in+i*len_inner, len_inner*sizeof(DT));
		for (int j = 0; j < len_inner; j++) {
			copy[j] = (in+i*len_inner)[j];
		}
		relu_map(in, im_res, len_inner);
		// memcpy(OUTPUT_res + i*len_inner, im_res, len_inner*sizeof(DT));
		for (int j = 0; j < len_inner; j++) {
			(OUTPUT_res+i*len_inner)[j] = im_res[j];
		}
	}
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
		// memcpy(input_layer, vals+o*size, size * sizeof(DT));
		for (int i = 0; i < size; i++) {
			input_layer[i] = (vals+o*size)[i];
		}
		int output_size = cols/2*rows/2;
		DT res_layer[output_size];
		max_pooling(input_layer, res_layer, cols, rows);
		// memcpy(OUTPUT_res+o*output_size, res_layer, output_size * sizeof(DT));
		for (int i = 0; i < output_size; i++) {
			(OUTPUT_res+o*output_size)[i] = (res_layer)[i];
		}
	}
}

DT mmulT_unrolled_inner(DT* a, DT* b, int common) { 
	DT sum = 0;
	
	int j = 0;
	// Add the first as groups of eight
	for (int i = 0; i+8<= common; i+=8) {
		sum += a[i+0]*b[i+0] + a[i+1]*b[i+1] + a[i+2]*b[i+2] + a[i+3]*b[i+3] + a[i+4]*b[i+4] + a[i+5]*b[i+5] + a[i+6]*b[i+6] + a[i+7]*b[i+7];
		j += 8;
	}
	if(j+4<=common) {
		sum += a[j+0]*b[j+0] + a[j+1]*b[j+1] + a[j+2]*b[j+2] + a[j+3]*b[j+3];
		j+=4;
	}
	for(int i = j; j < common; j++) {
		sum += a[j] * b[j];
	}

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
			OUTPUT_res[i*cols_b+j] = mmulT_unrolled_inner(aRow, bRow, common);
		}
	}
}




void convolution_naive(DT *image, DT* kernel, DT* OUTPUT_layer, int image_width, int window_size, int stride, int conv_width)
{
	int window_unrolled = window_size * window_size;
	// Need to assign each input pixel to the convolution matrix
	int x, y, wx, wy;
	for(y = 0; y < conv_width; y++) { // Inner position in the image
		for(x = 0; x < conv_width; x++) {
			int oPos = x+y*conv_width;
			DT tmp = 0;
			for(wy = 0; wy < window_size; wy++) {
				for(wx = 0; wx < window_size; wx++) {
					int convPos = wx+wy*window_size;
					tmp += kernel[convPos] * image[(y*stride + wy) * image_width + (x*stride + wx)];
				}				
			}
			OUTPUT_layer[oPos] = tmp;
		}
	}
}


void convolution_naive_outputs(DT *image, DT* kernels, DT* OUTPUT_layer, int image_width, int window_size, int output_size, int stride, int conv_width) {	
	//int res[conv_width*conv_width*];
	//DT_memset(OUTPUT_layer, conv_width*conv_width*output_size, 0);
	int kernel_size = window_size*window_size;
	for(int o = 0; o < output_size; o++) {
		DT kernel[kernel_size];
		DT res[conv_width*conv_width];
		// memcpy(kernel, kernels+ o*kernel_size, kernel_size * sizeof(DT));
		for (int i = 0; i < kernel_size; i++) {
			kernel[i] = (kernels+ o*kernel_size)[i];
		}

		convolution_naive(image, kernel, res, image_width, window_size, stride, conv_width);
		// memcpy(OUTPUT_layer + o*(conv_width*conv_width), res, conv_width*conv_width * sizeof(DT));
		for (int i = 0; i < conv_width*conv_width; i++) {
			(OUTPUT_layer + o*(conv_width*conv_width))[i] = res[i];
		}
	}
}

// Parameters taken from the paper
#define IMAGE_WIDTH 28
#define WINDOW_WIDTH 5
#define STRIDE 1
#define OUTPUT_CHANNELS 16

#define IMAGE_CROP (IMAGE_WIDTH - WINDOW_WIDTH + 1) // 28-5+1 = 24
#define SIZE_CONVOLUTION_1 (IMAGE_CROP * IMAGE_CROP) //Intermediate size (24^2 = 576
#define MAX_POOLING_WIDTH_1 (IMAGE_CROP / 2)//24/2=12

#define IMAGE_WIDTH_2 MAX_POOLING_WIDTH_1
#define MAX_POOLING_SIZE_1 (OUTPUT_CHANNELS*MAX_POOLING_WIDTH_1 * MAX_POOLING_WIDTH_1) // 16*12*12
#define IMAGE_CROP_2 (MAX_POOLING_WIDTH_1-WINDOW_WIDTH +1) // 12-5+1 = 8
#define SIZE_KERNELS_2 (WINDOW_WIDTH*WINDOW_WIDTH)  // 5*5 = 25 
#define SIZE_ALL_KERNELS_2 (SIZE_KERNELS_2 * OUTPUT_CHANNELS) // 16 * 25

#define SIZE_CONVOLUTION_2 (IMAGE_CROP_2*IMAGE_CROP_2) // 8*8 = 64
#define SIZE_RELU_2 OUTPUT_CHANNELS * IMAGE_CROP_2 * IMAGE_CROP_2 // 16 * 64

#define MAX_POOLING_WIDTH_2 (IMAGE_CROP_2 / 2) // 8/2 = 4
#define MAX_POOLING_SIZE_2 (OUTPUT_CHANNELS * MAX_POOLING_WIDTH_2 * MAX_POOLING_WIDTH_2)

#define FULLY_CONNECTED_WIDTH 100 // (7, 9)
#define FINAL_OUTPUT_CHANNELS 10


DT mmulT_unrolled_inner_2(DT* a, DT* b) { 
	DT sum = 0;

	// int j = 0;
	// // Add the first as groups of eight
	// for (int i = 0; i+8 < FULLY_CONNECTED_WIDTH; i+=8) {
	// 	sum += a[i+0]*b[i+0] + a[i+1]*b[i+1] + a[i+2]*b[i+2] + a[i+3]*b[i+3] + a[i+4]*b[i+4] + a[i+5]*b[i+5] + a[i+6]*b[i+6] + a[i+7]*b[i+7];
	// 	j += 8;
	// }
	// if (j+4 < FULLY_CONNECTED_WIDTH) {
	// 	sum += a[j+0]*b[j+0] + a[j+1]*b[j+1] + a[j+2]*b[j+2] + a[j+3]*b[j+3];
	// 	j+=4;
	// }
	// for(int i = j; j < FULLY_CONNECTED_WIDTH; j++) {
	// 	sum += a[j] * b[j];
	// }

	for(int i = 0; i < FULLY_CONNECTED_WIDTH; i++) {
		sum += a[i] * b[i];
	}

	return sum;
}


void mmulT_unrolled_2(DT* a, DT* b, DT *OUTPUT_res) {
	for(int i = 0; i < FINAL_OUTPUT_CHANNELS; i++) {
		DT aRow[FULLY_CONNECTED_WIDTH];
		// memcpy(aRow, a+i*common, common*sizeof(DT));
		for (int k = 0; k < FULLY_CONNECTED_WIDTH; k++) {
			aRow[k] = (a+i*FULLY_CONNECTED_WIDTH)[k];
		}

		for(int j = 0; j < 1; j++) {
			DT bRow[FULLY_CONNECTED_WIDTH];
			// memcpy(bRow, b+j*common, common*sizeof(DT));
			for (int k = 0; k < FULLY_CONNECTED_WIDTH; k++) {
				bRow[k] = (b+j*FULLY_CONNECTED_WIDTH)[k];
			}
			OUTPUT_res[i*1+j] = mmulT_unrolled_inner_2(aRow, bRow);
		}
	}
}

DT mmulT_unrolled_inner_1(DT* a, DT* b) { 
	DT sum = 0;
	
	// int j = 0;
	// // Add the first as groups of eight
	// for (int i = 0; i+8 < MAX_POOLING_SIZE_2; i+=8) {
	// 	sum += a[i+0]*b[i+0] + a[i+1]*b[i+1] + a[i+2]*b[i+2] + a[i+3]*b[i+3] + a[i+4]*b[i+4] + a[i+5]*b[i+5] + a[i+6]*b[i+6] + a[i+7]*b[i+7];
	// 	j += 8;
	// }
	// if(j+4< MAX_POOLING_SIZE_2) {
	// 	sum += a[j+0]*b[j+0] + a[j+1]*b[j+1] + a[j+2]*b[j+2] + a[j+3]*b[j+3];
	// 	j+=4;
	// }
	// for(int i = j; j < MAX_POOLING_SIZE_2; j++) {
	// 	sum += a[j] * b[j];
	// }

	for(int i = 0; i < MAX_POOLING_SIZE_2; i++) {
		sum += a[i] * b[i];
	}

	return sum;
}

void mmulT_unrolled_1(DT* a, DT* b, DT *OUTPUT_res) {
	for(int i = 0; i < FULLY_CONNECTED_WIDTH; i++) {
		DT aRow[MAX_POOLING_SIZE_2];
		// memcpy(aRow, a+i*common, common*sizeof(DT));
		for (int k = 0; k < MAX_POOLING_SIZE_2; k++) {
			aRow[k] = (a+i*MAX_POOLING_SIZE_2)[k];
		}

		for(int j = 0; j < 1; j++) {
			DT bRow[MAX_POOLING_SIZE_2];
			// memcpy(bRow, b+j*common, common*sizeof(DT));
			for (int k = 0; k < MAX_POOLING_SIZE_2; k++) {
				bRow[k] = (b+j*MAX_POOLING_SIZE_2)[k];
			}
			OUTPUT_res[i*1+j] = mmulT_unrolled_inner_1(aRow, bRow);
		}
	}
}

void sum_1(DT *OUTPUT_agg, DT* agg, DT *add) {
	for(int i = 0; i < OUTPUT_CHANNELS * SIZE_CONVOLUTION_2; i++) {
		OUTPUT_agg[i] = agg[i] + add[i];
	}
}

void convolution_naive_2(DT *image, DT* kernel, DT* OUTPUT_layer)
{
	int window_unrolled = WINDOW_WIDTH * WINDOW_WIDTH;
	// Need to assign each input pixel to the convolution matrix
	int x, y, wx, wy;
	for(y = 0; y < IMAGE_CROP_2; y++) { // Inner position in the image
		for(x = 0; x < IMAGE_CROP_2; x++) {
			int oPos = x+y*IMAGE_CROP_2;
			DT tmp = 0;
			for(wy = 0; wy < WINDOW_WIDTH; wy++) {
				for(wx = 0; wx < WINDOW_WIDTH; wx++) {
					int convPos = wx+wy*WINDOW_WIDTH;
					tmp += kernel[convPos] * image[(y*STRIDE + wy) * IMAGE_WIDTH_2 + (x*STRIDE + wx)];
				}				
			}
			OUTPUT_layer[oPos] = tmp;
		}
	}
}


void convolution_naive_outputs_2(DT *image, DT* kernels, DT* OUTPUT_layer) {	
	//int res[conv_width*conv_width*];
	//DT_memset(OUTPUT_layer, conv_width*conv_width*output_size, 0);
	int kernel_size = WINDOW_WIDTH*WINDOW_WIDTH;
	for(int o = 0; o < OUTPUT_CHANNELS; o++) {
		DT kernel[kernel_size];
		DT res[IMAGE_CROP_2*IMAGE_CROP_2];
		// memcpy(kernel, kernels+ o*kernel_size, kernel_size * sizeof(DT));
		for (int i = 0; i < kernel_size; i++) {
			kernel[i] = (kernels+ o*kernel_size)[i];
		}

		convolution_naive_2(image, kernel, res);
		// memcpy(OUTPUT_layer + o*(conv_width*conv_width), res, conv_width*conv_width * sizeof(DT));
		for (int i = 0; i < IMAGE_CROP_2*IMAGE_CROP_2; i++) {
			(OUTPUT_layer + o*(IMAGE_CROP_2*IMAGE_CROP_2))[i] = res[i];
		}
	}
}


void max_pooling_2(DT *vals, DT *OUTPUT_res) {
	int rows = IMAGE_CROP_2;
	int cols = IMAGE_CROP_2;
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

void max_pooling_outputs_2(DT *vals, DT *OUTPUT_res) {
	for(int o = 0; o < OUTPUT_CHANNELS; o++) {
		int size = IMAGE_CROP_2*IMAGE_CROP_2; 
		DT input_layer[size]; // We copy data, because compiler is unable to slice array efficiently
		// memcpy(input_layer, vals+o*size, size * sizeof(DT));
		for (int i = 0; i < size; i++) {
			input_layer[i] = (vals+o*size)[i];
		}
		int output_size = (IMAGE_CROP_2/2)*(IMAGE_CROP_2/2);
		DT res_layer[output_size];
		max_pooling_2(input_layer, res_layer);
		// memcpy(OUTPUT_res+o*output_size, res_layer, output_size * sizeof(DT));
		for (int i = 0; i < output_size; i++) {
			(OUTPUT_res+o*output_size)[i] = (res_layer)[i];
		}
	}
}

void max_pooling_1(DT *vals, DT *OUTPUT_res) {
	int rows = IMAGE_CROP;
	int cols = IMAGE_CROP;
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

void max_pooling_outputs_1(DT *vals, DT *OUTPUT_res) {
	for(int o = 0; o < OUTPUT_CHANNELS; o++) {
		int size = IMAGE_CROP*IMAGE_CROP; 
		DT input_layer[size]; // We copy data, because compiler is unable to slice array efficiently
		// memcpy(input_layer, vals+o*size, size * sizeof(DT));
		for (int i = 0; i < size; i++) {
			input_layer[i] = (vals+o*size)[i];
		}
		int output_size = IMAGE_CROP/2*IMAGE_CROP/2;
		DT res_layer[output_size];
		max_pooling_1(input_layer, res_layer);
		// memcpy(OUTPUT_res+o*output_size, res_layer, output_size * sizeof(DT));
		for (int i = 0; i < output_size; i++) {
			(OUTPUT_res+o*output_size)[i] = (res_layer)[i];
		}
	}
}

void relu_map_3(DT *in, DT *OUTPUT_res) {
	for(int i = 0; i < 1; i++) {
		OUTPUT_res[i] = relu(in[i]);
	}
}

void decomposed_relu_3(DT *in, DT *OUTPUT_res) {
	DT copy[1];
	DT im_res[1];
	for(int i = 0; i < FULLY_CONNECTED_WIDTH; i++) {
		// memcpy(copy, in+i*len_inner, len_inner*sizeof(DT));
		for (int j = 0; j < 1; j++) {
			copy[j] = (in+i*1)[j];
		}
		relu_map_3(in, im_res);
		// memcpy(OUTPUT_res + i*len_inner, im_res, len_inner*sizeof(DT));
		for (int j = 0; j < 1; j++) {
			(OUTPUT_res+i*1)[j] = im_res[j];
		}
	}
}

void relu_map_2(DT *in, DT *OUTPUT_res) {
	for(int i = 0; i < SIZE_CONVOLUTION_2; i++) {
		OUTPUT_res[i] = relu(in[i]);
	}
}

void decomposed_relu_2(DT *in, DT *OUTPUT_res) {
	DT copy[SIZE_CONVOLUTION_2];
	DT im_res[SIZE_CONVOLUTION_2];
	for(int i = 0; i < OUTPUT_CHANNELS; i++) {
		// memcpy(copy, in+i*len_inner, len_inner*sizeof(DT));
		for (int j = 0; j < SIZE_CONVOLUTION_2; j++) {
			copy[j] = (in+i*SIZE_CONVOLUTION_2)[j];
		}
		relu_map_2(in, im_res);
		// memcpy(OUTPUT_res + i*len_inner, im_res, len_inner*sizeof(DT));
		for (int j = 0; j < SIZE_CONVOLUTION_2; j++) {
			(OUTPUT_res+i*SIZE_CONVOLUTION_2)[j] = im_res[j];
		}
	}
}

void relu_map_1(DT *in, DT *OUTPUT_res) {
	for(int i = 0; i < SIZE_CONVOLUTION_1; i++) {
		OUTPUT_res[i] = relu(in[i]);
	}
}

void decomposed_relu_1(DT *in, DT *OUTPUT_res) {
	DT copy[SIZE_CONVOLUTION_1];
	DT im_res[SIZE_CONVOLUTION_1];
	for(int i = 0; i < OUTPUT_CHANNELS; i++) {
		// memcpy(copy, in+i*len_inner, len_inner*sizeof(DT));
		for (int j = 0; j < SIZE_CONVOLUTION_1; j++) {
			copy[j] = (in+i*SIZE_CONVOLUTION_1)[j];
		}
		relu_map_1(in, im_res);
		// memcpy(OUTPUT_res + i*len_inner, im_res, len_inner*sizeof(DT));
		for (int j = 0; j < SIZE_CONVOLUTION_1; j++) {
			(OUTPUT_res+i*SIZE_CONVOLUTION_1)[j] = im_res[j];
		}
	}
}

void convolution_naive_1(DT *image, DT* kernel, DT* OUTPUT_layer)
{
	int window_unrolled = WINDOW_WIDTH * WINDOW_WIDTH;
	// Need to assign each input pixel to the convolution matrix
	int x, y, wx, wy;
	for(y = 0; y < IMAGE_CROP; y++) { // Inner position in the image
		for(x = 0; x < IMAGE_CROP; x++) {
			int oPos = x+y*IMAGE_CROP;
			DT tmp = 0;
			for(wy = 0; wy < WINDOW_WIDTH; wy++) {
				for(wx = 0; wx < WINDOW_WIDTH; wx++) {
					int convPos = wx+wy*WINDOW_WIDTH;
					tmp += kernel[convPos] * image[(y*STRIDE + wy) * IMAGE_WIDTH + (x*STRIDE + wx)];
				}				
			}
			OUTPUT_layer[oPos] = tmp;
		}
	}
}

void convolution_naive_outputs_1(DT *image, DT* kernels, DT* OUTPUT_layer) {	
	//int res[conv_width*conv_width*];
	//DT_memset(OUTPUT_layer, conv_width*conv_width*output_size, 0);
	int kernel_size = WINDOW_WIDTH*WINDOW_WIDTH;
	for(int o = 0; o < OUTPUT_CHANNELS; o++) {
		DT kernel[kernel_size];
		DT res[IMAGE_CROP*IMAGE_CROP];
		// memcpy(kernel, kernels+ o*kernel_size, kernel_size * sizeof(DT));
		for (int i = 0; i < kernel_size; i++) {
			kernel[i] = (kernels + o*kernel_size)[i];
		}

		convolution_naive_1(image, kernel, res);
		// memcpy(OUTPUT_layer + o*(conv_width*conv_width), res, conv_width*conv_width * sizeof(DT));
		for (int i = 0; i < IMAGE_CROP*IMAGE_CROP; i++) {
			(OUTPUT_layer + o*(IMAGE_CROP*IMAGE_CROP))[i] = res[i];
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
	DT kernelsL2[OUTPUT_CHANNELS * SIZE_KERNELS_2]; // (16 * 
	DT kernelsFC1[FULLY_CONNECTED_WIDTH * MAX_POOLING_SIZE_2]; // (16 * 4 * 4) * 100 = 256 * 100
	DT kernelsFC2[FINAL_OUTPUT_CHANNELS * FULLY_CONNECTED_WIDTH]; // 100 * 10
} InputB;

typedef struct
{
	DT final_layer[FINAL_OUTPUT_CHANNELS];
	//DT final_layer[MAX_POOLING_SIZE_1];
} Output;

void sum(DT *OUTPUT_agg, DT* agg, DT *add, int len) {
	for(int i = 0; i < len; i++) {
		OUTPUT_agg[i] = agg[i] + add[i];
	}
}

Output main(
	__attribute__((private(0))) DT image[IMAGE_WIDTH * IMAGE_WIDTH], 
	__attribute__((private(1))) DT kernelsL1[OUTPUT_CHANNELS * WINDOW_WIDTH * WINDOW_WIDTH], 
	__attribute__((private(1))) DT kernelsL2[OUTPUT_CHANNELS * SIZE_KERNELS_2], 
	__attribute__((private(1))) DT kernelsFC1[FULLY_CONNECTED_WIDTH * MAX_POOLING_SIZE_2], 
	__attribute__((private(1))) DT kernelsFC2[FINAL_OUTPUT_CHANNELS * FULLY_CONNECTED_WIDTH])
{
	InputA INPUT_A;
	INPUT_A.image = image;

	InputB INPUT_B;
	INPUT_B.kernelsL1 = kernelsL1;
	INPUT_B.kernelsL2 = kernelsL2;
	INPUT_B.kernelsFC1 = kernelsFC1;
	INPUT_B.kernelsFC2 = kernelsFC2;

	DT convolution_layer[OUTPUT_CHANNELS * SIZE_CONVOLUTION_1];
	DT convolution_relu[OUTPUT_CHANNELS * SIZE_CONVOLUTION_1];

	Output output;

	// Convolution (1)
	// DT* kernels, DT* OUTPUT_layer, int image_width, int window_size, int output_size, int stride, int conv_width) {	
	convolution_naive_outputs_1(INPUT_A.image, INPUT_B.kernelsL1, convolution_layer);
	
	// Relu (2)
	// for(int i = 0; i < OUTPUT_CHANNELS * SIZE_CONVOLUTION_1; i++) {
	decomposed_relu_1(convolution_layer, convolution_relu);

	// Max pooling (3)
	DT pooling_layer[MAX_POOLING_SIZE_1]; // Size is 16 * 12 *12
	max_pooling_outputs_1(convolution_relu, pooling_layer);	
	
	DT convolution_layer_2[OUTPUT_CHANNELS * SIZE_CONVOLUTION_2]; // 16 * (8*8)
	DT convolution_relu_2[OUTPUT_CHANNELS * SIZE_CONVOLUTION_2]; // 16 * (8*8)
	// DT_memset(convolution_layer_2, OUTPUT_CHANNELS * SIZE_CONVOLUTION_2, 0);
	for (int i = 0; i < OUTPUT_CHANNELS * SIZE_CONVOLUTION_2; i++) {
		convolution_layer_2[i] = 0;
	}

	for(int o = 0; o < OUTPUT_CHANNELS; o++) { // Accumulate convolutions
		DT convolution_layer_tmp[OUTPUT_CHANNELS * SIZE_CONVOLUTION_2]; // 16 * (8*8)
		DT convolution_layer_tmp_2[OUTPUT_CHANNELS * SIZE_CONVOLUTION_2]; // 16 * (8*8)
		DT image[IMAGE_WIDTH_2*IMAGE_WIDTH_2]; // 12*12=144
		DT kernels[SIZE_ALL_KERNELS_2];
		// memcpy(kernels, INPUT_B.kernelsL2, SIZE_ALL_KERNELS_2*sizeof(DT));
		for (int i = 0; i < SIZE_ALL_KERNELS_2; i++) {
			kernels[i] = INPUT_B.kernelsL2[i];
		}
		// memcpy(image, pooling_layer+o*IMAGE_WIDTH_2*IMAGE_WIDTH_2, IMAGE_WIDTH_2*IMAGE_WIDTH_2*sizeof(DT));
		for (int i = 0; i < IMAGE_WIDTH_2*IMAGE_WIDTH_2; i++) {
			image[i] = (pooling_layer+o*IMAGE_WIDTH_2*IMAGE_WIDTH_2)[i];
		}

		convolution_naive_outputs_2(image, kernels, convolution_layer_tmp);
		sum_1(convolution_layer_tmp_2, convolution_layer_2, convolution_layer_tmp);
		// memcpy(convolution_layer_2, convolution_layer_tmp_2, OUTPUT_CHANNELS * SIZE_CONVOLUTION_2);
		for (int i = 0; i < OUTPUT_CHANNELS * SIZE_CONVOLUTION_2; i++) {
			convolution_layer_2[i] = convolution_layer_tmp_2[i];
		}
	}
	
	decomposed_relu_2(convolution_layer_2, convolution_relu_2);
	
	// Max pooling (6)
	DT pooling_layer_2[MAX_POOLING_SIZE_2]; // Size is 16 * 4 * 4
	max_pooling_outputs_2(convolution_relu_2, pooling_layer_2);	
	
	// FC (7)
	DT fc_layer[FULLY_CONNECTED_WIDTH];
	//DT_memset(pooling_layer_2, MAX_POOLING_SIZE_2, 2);
	mmulT_unrolled_1(INPUT_B.kernelsFC1, pooling_layer_2, fc_layer);

	// RELU (8)
	DT fc_relu[FULLY_CONNECTED_WIDTH];
	decomposed_relu_3(fc_layer, fc_relu);
	
	// Temporary output
	//	memcpy(output.final_layer, pooling_layer_2, FINAL_OUTPUT_CHANNELS*sizeof(DT));

	mmulT_unrolled_2(INPUT_B.kernelsFC2, fc_layer, output.final_layer);

	return output;
}
