# Associative-Commutative Common-Subexpression-Elimination

The idea here is to optimize expressions like `x * y * z + y * x` by being
sure to only compute `y * x` once.

More formally (after flattening) we have a big DAG of computation steps, where
some steps apply a *commutative*, *associative* operator (e.g. addition,
multiplication, and, or, XOR, ...) to a set of inputs. Note that these
operators are n-ary. The idea is to restructure the DAG using *binary*
operations, while minimizing the total number of binary operations.

This is probably NP-hard in general (or at least, it's decision problem is),
but I'm sure we can find some good heuristics. There is *some* prior work, but
it's a lot less well-done than you might think. See:

* (really simple/probably bad heuristic, but has proven bounds) https://arxiv.org/abs/2102.01730
* (probably better, but no bounds) https://link.springer.com/content/pdf/10.1007%2F978-3-319-10428-7_43.pdf
* (probably better, but no bounds) https://link.springer.com/content/pdf/10.1007%2F978-3-540-85958-1_23.pdf

Project plan:
1. Implement the 3 above algorithms as IR-to-IR transformations
2. Measure their effect, e.g., on the ZoK standard library
   * We should expect wins, especially on things like Edwards curve arithmetic
3. Invent your own heuristics and measure their effect
4. Do a cool write-up explaining the compile-time/optimization trade-off of
   these different approaches.
