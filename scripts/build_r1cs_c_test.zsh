#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --example circ

BIN=./target/release/examples/circ

case "$OSTYPE" in 
    darwin*)
        alias measure_time="gtime --format='%e seconds %M kB'"
    ;;
    linux*)
        alias measure_time="time --format='%e seconds %M kB'"
    ;;
esac

function r1cs_test {
    cpath=$1
    measure_time $BIN $cpath r1cs --action count
}

r1cs_test ./examples/C/r1cs/add.c

