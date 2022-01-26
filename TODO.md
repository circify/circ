Passes to write:

[ ] shrink bit-vectors using range analysis.
  * IR analysis infrastructure
  * shrink comparisons too
    * generalized version of constant comparison?
[ ] FE analysis infrastructure
[ ] common sub-expression grouping
  * for commutative/associative ops?
  * after flattening
  * Perhaps one of these algs:
    * https://link.springer.com/content/pdf/10.1007%2F978-3-319-10428-7_43.pdf
    * https://link.springer.com/content/pdf/10.1007%2F978-3-540-85958-1_23.pdf
[ ] array flattening
[ ] permutation-based memory checking
  * perhaps included: verifier challenges?
[ ] printing with global letification cfg
[ ] table-based word-splitting for cheap math in R1CS
  * depends on good lookups
[ ] SMT based FE testing
[ ] General FE to interpreter
[ ] Improving/parameterizing our IR term distribution
  * We use it to fuzz IR passes
  * General problem: Fuzzing language FEs
[ ] Recursive proving.
[ ] Incorporate verifier challenges.
[ ] Support functions in the compiler.
[ ] Equality saturation/e-graphs?


Bigger research questions:
[ ] SoK: compiling to R1CS
  * focus on embedding complex datatypes:
    * use lookups
[ ] Compiling to branching programs
