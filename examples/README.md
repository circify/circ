# CirC examples

## `ztest.rs` — Unit-test circuits written in ZoKratesCurly

`ztest` discovers and runs `@test` functions in a ZoKratesCurly (`.zok`) program.
Each test is compiled to R1CS on its own and its assertions are checked with a
proof backend, so a test passes only if the circuit is satisfiable for the given
inputs.

**Step 1: Write tests**

Annotate test functions with:

```
@test(backend = {groth16, mirage}) <input1> = <val1>, <input2> = <val2>, ...;
```

See [ZoKratesCurly/pf/ztest/coverage_test.zok](ZoKratesCurly/pf/ztest/coverage_test.zok)
for a worked example covering backend selection, scalar/array/tuple inputs, and
public/private visibility.

Rules for an annotated function:

- The backend defaults to `groth16` and may be omitted.
- It behaves like `main`: it must have no generics and no return value.
- It must make assertions (that is what the test verifies).

**Step 2: Run tests**

Build with the features the backends need, then point `ztest` at a file:

```
cargo run --example ztest --features smt,zokc,bellman -- \
  examples/ZoKratesCurly/pf/ztest/coverage_test.zok
```
