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
fhe_test ./examples/C/fhe/unit_tests/boolean_tests/2pc_boolean_and.c
fhe_test ./examples/C/fhe/unit_tests/boolean_tests/2pc_boolean_or.c