#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --release --example circ_c

BIN=./target/release/examples/circ_c

case "$OSTYPE" in 
    darwin*)
        alias measure_time="gtime --format='%e seconds %M kB'"
    ;;
    linux*)
        alias measure_time="time --format='%e seconds %M kB'"
    ;;
esac

function mpc_test {
    parties=$1
    zpath=$2
    RUST_BACKTRACE=1 measure_time $BIN -p $parties $zpath
}

# build mpc arithmetic tests
mpc_test 2 ./examples/C/mpc/unit_tests/arithmetic_tests/2pc_add.c