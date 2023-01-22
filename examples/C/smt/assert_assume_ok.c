int main(
    __attribute__((private(0))) int a,
    __attribute__((private(1))) int b)
{
    __VERIFIER_assume(a != b);
    __VERIFIER_assert((a ^ b) != 0);
}
