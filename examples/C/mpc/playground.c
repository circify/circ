int main(
    __attribute__((private(0))) int x,
    __attribute__((private(0))) int y,
    __attribute__((private(1))) int z,
    __attribute__((private(1))) int w,
    __attribute__((private(2))) int c1,
    __attribute__((private(2))) int c2
)
{
    int plain = c1 * c2;
    int p1 = x + y + x * y * c1;
    int p2 = z + w + z * w * c2;
    
    int m = p1 * p2;

    return m + plain;
}