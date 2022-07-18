
typedef struct
{
	int a;
    int b;
} Output;

Output main(
    __attribute__((private(0))) int a,
    __attribute__((private(1))) int b)
{
    Output c;
    c.a = a;
    c.b = b;
    return c;
}