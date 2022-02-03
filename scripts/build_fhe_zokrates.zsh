#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --release --example circ

BIN=./target/release/examples/circ

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
    ipath=$2
    RUST_BACKTRACE=1 measure_time $BIN $zpath --inputs $ipath fhe
}

# build fhe boolean tests
fhe_test ./examples/ZoKrates/fhe/unit_tests/boolean_tests/fhe_and.zok ./examples/ZoKrates/fhe/inputs/fhe_and.txt