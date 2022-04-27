#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features c --example circ 

BIN=./target/release/examples/circ
export CARGO_MANIFEST_DIR=$(pwd)

case "$OSTYPE" in 
    darwin*)
        alias measure_time="gtime --format='%e seconds %M kB'"
    ;;
    linux*)
        alias measure_time="time --format='%e seconds %M kB'"
    ;;
esac

function fhe_test {
    cpath=$1
    RUST_BACKTRACE=1 measure_time $BIN $cpath fhe
}

# build boolean tests
fhe_test ./examples/C/fhe/unit_tests/boolean_tests/boolean_and.c
fhe_test ./examples/C/fhe/unit_tests/boolean_tests/boolean_or.c
fhe_test ./examples/C/fhe/unit_tests/boolean_tests/boolean_equals.c

# build nary boolean tests
fhe_test ./examples/C/fhe/unit_tests/nary_boolean_tests/nary_boolean_and.c

# build arithmetic tests
fhe_test ./examples/C/fhe/unit_tests/arithmetic_tests/add.c
fhe_test ./examples/C/fhe/unit_tests/arithmetic_tests/mult.c
fhe_test ./examples/C/fhe/unit_tests/arithmetic_tests/mult_add_pub.c

# build nary arithmetic tests
fhe_test ./examples/C/fhe/unit_tests/nary_arithmetic_tests/nary_arithmetic_add.c