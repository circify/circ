int main(
    __attribute__((private(0))) int a,
    __attribute__((private(1))) int b)
{
  __VERIFIER_assume(b > 0 && b < 31);
  int x = a << b;
  return x;
}
