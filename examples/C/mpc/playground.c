
typedef struct
{
	int res[2];
} Output;


Output main() {
    int a[2] = {1,1};
    int b[2] = {2,2};

    Output o;
    // o.res[0] = a[0] + b[0];
    // o.res[1] = a[1] + b[1];

    o.res = VecAdd(a, b);
    return o;
}
