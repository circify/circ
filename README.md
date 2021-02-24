# CirC: The Circuit Compiler

This repository holds an in-progress rewrite of CirC.

CirC is a *compiler infrastructure* which supports compilation from
high-level (stateful, uniform) languages to (existentially quantified)
circuits.

## Requirements

Developing CirC requires the CVC4 SMT solver, which is used in some tests. Its
binary must be on your path. On Arch Linux and Ubuntu you can install the
`cvc4` package from official repositories.

## Todo List

- [x] draft circify
- [ ] Intern variable names
- [x] Optimize R1CS
- [x] Inlining optimization
- [x] ZoKrates FE
- [ ] C FE
- [ ] Tune optimizer for ouput, speed, and memory usage.
- [ ] More SMT solver support
- [ ] More eval support
