# CirC: The Circuit Compiler

This repository holds an in-progress rewrite of CirC.

CirC is a *compiler infrastructure* which supports compilation from
high-level (stateful, uniform) languages to (existentially quantified)
circuits.

## Requirements

Developing CirC requires the CVC4 SMT solver, which is used in some tests. Its
binary must be on your path. On Arch Linux and Ubuntu you can install the
`cvc4` package from official repositories.

## Architecture

* Components:
  * `src/ir`
    * IR term definition
      * `term/bv.rs`: bit-vec literals
      * `term/field.rs`: prime-field literals
      * `term/ty.rs`: type-checking
      * `term/extras.rs`: algorithms: substitutions, etc.
    * Optimization
      * `opt/cfold.rs`: constant folding
      * `opt/flat.rs`: n-ary flattening
      * `opt/inline.rs`: inlining
      * `opt/sha.rs`: replacements for SHA's CH and MAJ operations
      * `opt/mem/obliv.rs`: oblivious array elimination
      * `opt/mem/lin.rs`: linear-scan array elimination
      * `opt/mem/visit.rs`: utility for visiting (and replacing?) all
         array-related terms
  * `src/target`
    * R1CS backend
      * lowering from IR
      * optimization
      * connection to bellman
    * SMT backend
      * based on rsmt2
  * `src/circify`
    * Machinery for recursive imports
    * `mem`: the stack memory module
    * `mod`: the main Circify interface
  * `src/front`
    * `zokrates`: the ZoKrates front-end
  * `src/util`
    * A once-queue (each item appears at most once)
      * Implemented by combining a set with a queue
    * hash-consing machinery
  * `examples/circ.rs`
    * This is the entry point to the zokrates copiler

## Todo List

- [ ] Intern variable names
- [ ] Tweak log system to expect exact target match
- [ ] C FE
- [ ] Tune optimizer for ouput, speed, and memory usage.
- [ ] More SMT solver support
