Concrete:
[ ] R1CS optimizations
  * reduce linearity without recip
  * don't debitify eagerly
  * cache pf lits?
  * LCs as vectors
[ ] shrink bit-vectors using range analysis.
  * IR analysis infrastructure
  * shrink comparisons too
    * generalized version of constant comparison?
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
[ ] Implement sorts using hash-consing.
[ ] Modeling RAM transformations in Coq and proving their correctness
  1. model a term IR, with functional arrays (like ours!).
  2. model a RAM-augmented term IR, with conditional stores and reads
  3. write a converter
  4. prove that it works 

Vague:
[ ] FE analysis infrastructure
[ ] Recursive proving.
[ ] Incorporate verifier challenges.
[ ] Support functions in the compiler.
[ ] Equality saturation/e-graphs?


Small research questions:
[ ] Model a RAM-extraction pass in Coq and prove it correct.
  * input: a term-graph computation that uses functional arrays
  * output: a term-graph computation that has RAM transcripts attached, has
    *no* array sorts, and is provably equivalent.
  * Passes that are likely important:
    * Replace array variables with mass stores
    * Lift tuples out of arrays with AoS -> SoA transformation
    * Scalarize array equality with a big AND of EQ
    * Flatten nested arrays? I haven't though this out. Requires scalarizing some stores/selects.
    * Do a RAM extraction pass that assumes all arrays have primitive keys and value.
[ ] Model a RAM-extraction pass in Coq and prove it correct.
  * pretty printing term DAGs with letification
  * Like LaTeX meets letification.

Bigger research questions:
[ ] SoK: compiling to R1CS
  * focus on embedding complex datatypes:
    * use lookups
[ ] Compiling to branching programs
