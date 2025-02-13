# Quickstart for ZKPs using the Z# front-end

1. Configure CirC's example compiler: `./driver.py --features bellman r1cs poly zok`
  * turns on the [bellman](https://github.com/zkcrypto/bellman/) ZKP backend,
     the R1CS compiler extension needed to target it,
     support for finite field polynomials,
     and the Z# (an extended ZoKrates) frontend
2. Build the CirC library and example compiler `./driver.py -b`
3. Compile an example program to ZKPs and sample ZKP paramaters: `./target/release/examples/circ examples/ZoKrates/pf/maj.zok r1cs --action setup`
  * creates a proving key in file `./P`
  * creates a verifying key in file `./V`
  * The program does a bitwise majority of three 8-bit arguments; the inputs are secret, the output is public.
4. Create a proof: `./target/release/examples/zk --inputs examples/ZoKrates/pf/maj.zok.pin --action prove`
  * creates a proof in file `./pi`
  * the (secret) program inputs are in the input file `examples/ZoKrates/pf/maj.zok.pin`
5. Verify the proof against a claimed program output: `./target/release/examples/zk --inputs examples/ZoKrates/pf/maj.zok.vin --action verify`
  * the output is `return` in the input file `examples/ZoKrates/pf/maj.zok.vin`
  * if verification fails, the command will return an error
