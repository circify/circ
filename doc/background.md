# Background Reading for CirC

* IR
   * The IR is based on SMT
      * [Tutorial](https://rise4fun.com/z3/tutorial)
      * [Standard](http://smtlib.cs.uiowa.edu/standard.shtml)
   * The IR is implemented using "perfect sharing" aka "hash consing"
      * [Wikipedia](https://en.wikipedia.org/wiki/Hash_consing)
      * Our implementation is based on
         [this](https://docs.rs/hashconsing/1.3.0/hashconsing/)
