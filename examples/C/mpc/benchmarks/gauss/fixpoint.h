#define FIXEDPOINT_BITS 32
#define FIXEDPOINT_INTEGER_BITS 24
#define FIXEDPOINT_FRACTION_BITS (FIXEDPOINT_BITS - FIXEDPOINT_INTEGER_BITS)

typedef int fixedpt;
typedef int fixedptd;

fixedptd fixedpt_mul_inner(fixedpt a, fixedpt b)
{
	return (fixedptd)a * (fixedptd)b;
}

fixedpt fixedpt_mul(fixedpt a, fixedpt b)
{
	return  (fixedptd)(fixedpt_mul_inner(a,b) >> (fixedptd)FIXEDPOINT_FRACTION_BITS);
}

fixedpt fixedpt_div(fixedpt a, fixedpt b)
{
	return ((fixedptd)a << FIXEDPOINT_FRACTION_BITS) / b;
}
