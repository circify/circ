# zsharp (nee zok07) interpreter quickstart

**WARNING** this interpreter is still experimental! When things break, please
tell me about them :)

## building

1. see `scripts/dependencies_*` for info on installing deps.

   Note that on M1 macs the homebrew instructions don't quite work, because
   the coin-or build from homebrew is broken (for now). Don't worry---you
   don't actually need this dep to build the zsharp interpreter.

2. circ uses some experimental APIs, so you'll need rust nightly!

3. To build the Z# interpreter cli,
   `cargo build --release --example zxi --no-default-features --features smt,zok`
   
   Alternatively, you can try our new driver script.
   To set the required features for zxi and zxc,
   `python3 driver.py -F smt zok`
   To build,
   `python3 driver.py -b` 

## running

After building as above, `target/release/examples/zxi` will have been
generated. This executable takes one argument, the name of a .zok file.
Absolute and relative paths are both OK:

    target/release/examples/zxi /tmp/foo.zok
    target/release/examples/zxi ../../path/to/somewhere/else.zok

You may want to set the `RUST_LOG` environment variable to see more info
about the typechecking and interpreting process:

    RUST_LOG=debug target/release/examples/zxi /tmp/foo.zok
