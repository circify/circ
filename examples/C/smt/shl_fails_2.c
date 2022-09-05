int main(
    __attribute__((private(0))) int a,
    __attribute__((private(1))) int b)
{
  // TODO: the property shouldn't hold, even with the assumption. However, it
  // does hold with the assumption b/c the < in the assumption is incorrectly
  // understood as unsigned.
  // __VERIFIER_assume(b < 10);
  int x = a << b;
  return x;
}
