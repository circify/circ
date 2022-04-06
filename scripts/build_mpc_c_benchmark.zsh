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

function mpc_test {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc 
}

mpc_test 2 ./examples/C/mpc/benchmarks/2pc_biomatch.c --cost-model $1 --selection-scheme $2
