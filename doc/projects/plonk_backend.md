# Plonk Backend

Plonk[1] is a zkSNARK. You can find an implementation of it here[2].

Plonk is different from traditional zkSNARKs in that the class of relations
that it supports is slightly different. First, it supports relation expressed
as *binary arithmetic circuits* with private and public inputs/outputs instead
of R1CS. Second, it also supports so-called "custom gates" in these circuits.
For example, you could add a gate that multiplies 3 numbers instead of 2, or
that requires a value to be 0 or 1, etc.

It would be good to have a Plonk back-end for CirC, so that we could use CirC
to do research into compiling with custom gates.

Rough project plan:

1. Compile to Plonk relations (no custom gates)
  * Write an IR-to-IR pass that turns a bool/bit-vector/field computation
    into a plonk-style arithmetic circuit (field computation).
    * It may be useful to base this pass on the IR-to-R1CS translation[3]
      * Specifically, look at how bit-vectors and booleans are embedded in the
        field
  * Hook up our IR to a plonk back-end. For example, [2].
2. Compile to Plonk relations (user-provided custom gates)
  * Add a "undefined function call" operator to the IR[4].
  * Define a set of plonk-friend custom-gates that the back-end can handle
  * Expose these to the programmer in *some* front-end.
  * Try to use these to write interesting programs!
    * Probable a hash function (e.g., SHA, Rescue, or Pedersen) would be a
      good idea.
3. Introduce useful custom gates *in the compiler*

[1]: https://eprint.iacr.org/2019/953
[2]: https://github.com/ZK-Garage/plonk
[3]: https://github.com/circify/circ/blob/master/src/target/r1cs/trans.rs
[4]: https://github.com/circify/circ/blob/master/src/ir/term/mod.rs#L47
