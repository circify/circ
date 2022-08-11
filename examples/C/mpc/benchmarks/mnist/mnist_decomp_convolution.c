/* Neural Network according to Figure 12 of MiniONN 
	Assumes image to be square, assume window size to be odd
*/

typedef int DT;

void convolution_naive_2(DT *image, DT* kernel, DT* OUTPUT_layer)
{
	int window_unrolled = 5 * 5;
	// Need to assign each input pixel to the convolution matrix
	int x, y, wx, wy;
	for(y = 0; y < 8; y++) { // Inner position in the image
		for(x = 0; x < 8; x++) {
			int oPos = x+y*8;
			DT tmp = 0;
			for(wy = 0; wy < 5; wy++) {
				for(wx = 0; wx < 5; wx++) {
					int convPos = wx+wy*5;
					tmp += kernel[convPos] * image[(y*1 + wy) * 12 + (x*1 + wx)];
				}				
			}
			OUTPUT_layer[oPos] = tmp;
		}
	}
}
void convolution_naive_outputs_2(DT *image, DT* kernels, DT* OUTPUT_layer) {	
	//int res[conv_width*conv_width*];
	//DT_memset(OUTPUT_layer, conv_width*conv_width*output_size, 0);
	int kernel_size = 5*5;
	for(int o = 0; o < 1; o++) {
		DT kernel[kernel_size];
		DT res[8*8];
		// memcpy(kernel, kernels+ o*kernel_size, kernel_size * sizeof(DT));
		for (int i = 0; i < kernel_size; i++) {
			kernel[i] = (kernels+o*kernel_size)[i];
		}
		// convolution_naive_2(image, kernel, res, image_width, window_size, stride, conv_width);
		convolution_naive_2(image, kernel, res);
		// memcpy(OUTPUT_layer + o*(conv_width*conv_width), res, conv_width*conv_width * sizeof(DT));
		for (int i = 0; i < 8*8; i++) {
			(OUTPUT_layer + o*(8*8))[i] = res[i];
		}
	}
}	


void convolution_naive_1(DT *image, DT* kernel, DT* OUTPUT_layer)
{
	int window_unrolled = 5 * 5;
	// Need to assign each input pixel to the convolution matrix
	int x, y, wx, wy;
	for(y = 0; y < 24; y++) { // Inner position in the image
		for(x = 0; x < 24; x++) {
			int oPos = x+y*24;
			DT tmp = 0;
			for(wy = 0; wy < 5; wy++) {
				for(wx = 0; wx < 5; wx++) {
					int convPos = wx+wy*5;
					tmp += kernel[convPos] * image[(y*1 + wy) * 28 + (x*1 + wx)];
				}				
			}
			OUTPUT_layer[oPos] = tmp;
		}
	}
}
void convolution_naive_outputs_1(DT *image, DT* kernels, DT* OUTPUT_layer) {	
	//int res[conv_width*conv_width*];
	//DT_memset(OUTPUT_layer, conv_width*conv_width*output_size, 0);
	int kernel_size = 5*5;
	for(int o = 0; o < 16; o++) {
		DT kernel[kernel_size];
		DT res[24*24];
		// memcpy(kernel, kernels+ o*kernel_size, kernel_size * sizeof(DT));
		for (int i = 0; i < kernel_size; i++) {
			kernel[i] = (kernels+ o*kernel_size)[i];
		}
		convolution_naive_1(image, kernel, res);
		// memcpy(OUTPUT_layer + o*(conv_width*conv_width), res, conv_width*conv_width * sizeof(DT));
		for (int i = 0; i < 24*24; i++) {
			(OUTPUT_layer + o*(24*24))[i] = res[i];
		}
	}
}

int main(
	__attribute__((private(0))) DT INPUT_A_image1[784],
    __attribute__((private(0))) DT INPUT_A_image2[144], 
	__attribute__((private(1))) DT INPUT_B_kernel1[400], 
	__attribute__((private(1))) DT INPUT_B_kernel2[400] 
)
{
	DT res1[9216];
	DT res2[1024];

	// Convolution (1)
	//, DT* kernels, DT* OUTPUT_layer, int image_width, int window_size, int output_size, int stride, int conv_width) {	
	// convolution_naive_outputs(INPUT_A_image1, INPUT_B_kernel1, res1, 28, 5, 16, 1, 24);
	convolution_naive_outputs_1(INPUT_A_image1, INPUT_B_kernel1, res1);
	// convolution_naive_outputs(INPUT_A_image2, INPUT_B_kernel2, res2, 12, 5, 16, 1, 8);
	convolution_naive_outputs_2(INPUT_A_image2, INPUT_B_kernel2, res2);
	
	DT OUTPUT_sum = res1[0] + res2[1];
	return OUTPUT_sum;
}
