#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features smt,zok --example circ

BIN=./target/release/examples/circ
#export CARGO_MANIFEST_DIR=$(pwd)

case "$OSTYPE" in 
    darwin*)
        alias measure_time="gtime --format='%e seconds %M kB'"
    ;;
    linux*)
        alias measure_time="time --format='%e seconds %M kB'"
    ;;
esac

function fhe_test {
    zpath=$1
    RUST_BACKTRACE=1 measure_time $BIN $zpath fhe
}

# build boolean tests
fhe_test ./examples/ZoKrates/fhe/unit_tests/boolean_tests/boolean_and.zok
fhe_test ./examples/ZoKrates/fhe/unit_tests/boolean_tests/boolean_or.zok 
fhe_test ./examples/ZoKrates/fhe/unit_tests/boolean_tests/boolean_equals.zok 

# build nary boolean tests
fhe_test ./examples/ZoKrates/fhe/unit_tests/nary_boolean_tests/nary_boolean_and.zok

# build arithmetic tests
fhe_test ./examples/ZoKrates/fhe/unit_tests/arithmetic_tests/add.zok
fhe_test ./examples/ZoKrates/fhe/unit_tests/arithmetic_tests/mult.zok
fhe_test ./examples/ZoKrates/fhe/unit_tests/arithmetic_tests/mult_add_pub.zok

# build nary arithmetic tests
fhe_test ./examples/ZoKrates/fhe/unit_tests/nary_arithmetic_tests/nary_arithmetic_add.zok

