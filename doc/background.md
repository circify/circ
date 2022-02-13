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
* IR Grammar
  * Lexical structure
    * Lexemes are:
      * structural symbols: `'('`, `')'`
      * keywords: `let`
      * literals: `regex'#x[0-9a-fA-F]+'`, `regex'#b[01]+'`, `regex'-?[1-9][0-9]*'`
        * Note: not all IR values have their own literal
      * identifiers: `regex'[a-zA-Z_][a-zA-Z0-9_]'`
      * whitespace is ignored
  * Syntactic structure
    * Terminals: ID, HEX, BIN, NAT, (, ), LET
    *
