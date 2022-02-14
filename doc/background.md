# Background Reading for CirC

* IR
   * The IR is based on SMT
      * [Tutorial](https://rise4fun.com/z3/tutorial)
      * [Standard](http://smtlib.cs.uiowa.edu/standard.shtml)
   * The IR is implemented using "perfect sharing" aka "hash consing"
      * [Wikipedia](https://en.wikipedia.org/wiki/Hash_consing)
      * Our implementation is based on
         [this](https://docs.rs/hashconsing/1.3.0/hashconsing/)
   * Serialization
      * s-expressions
      * constants
        * bool -> true, false
        * bv -> #xXX, #bBBBB
        * fp -> Rust FP literals
        * int -> decimal literal
        * tuple -> (tuple_value ...)
        * array -> (array_value KEY_SORT DEFAULT SIZE ASSOC_LIST)
        * ASSOC_LIST =
      * sorts
      * higher-order operators
* IR Textual format
  * It's s-expressions.
  * `N`: natural number
  * `I`: integer (arbitrary-precision)
  * `X`: identifier
    * regex: `[^()0-9#; \t\n\f][^(); \t\n\f#]*`
  * Sort `S`:
    * `bool`
    * `f32`
    * `f64`
    * `(bv N)`
    * `(mod I)`
    * `(tuple S1 ... Sn)`
    * `(array Sk Sv N)`
  * Value `V`:
    * boolean: `true`, `false`
    * integer: `I`
    * bit-vector: `#xFFFF...`, `#bBBBB...`
    * field literal: `#fDD` or `#fDDmDD`.
      * In the former case, an ambient modulus must be set.
    * tuple: `(#t V1 ... Vn)`
    * array: `(#a Sk V N ((Vk1 Vv1) ... (Vkn Vvn)))`
  * Term `T`:
    * value: `V`
    * let: `(let ((X1 T1) ... (Xn Tn)) T)`
    * declare: `(declare ((X1 S1) ... (Xn Sn)) T)`
    * set_default_modulus: `(set_default_modulus I T)`
    * set_default_modulus: `(O T1 ... TN)`
  * Operator `O`:
    * Plain operators (TODO)
    * `(field N)`
    * `(update N)`
    * `(sext N)`
    * `(uext N)`
    * `(bit N)`
    * TODO: more
