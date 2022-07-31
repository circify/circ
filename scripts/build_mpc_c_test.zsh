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
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "lp"
}

function mpc_test_2  {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "a+b"
}

function mpc_test_3 {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "gglp"
}


function mpc_test_4 {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "lp+mut" --num-parts 12 --mut-level 4 --mut-step-size 1 --graph-type 0
}

function mpc_test_5 {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "lp+mut" --num-parts 48 --mut-level 4 --mut-step-size 1 --graph-type 0
}

function mpc_test_bool  {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "b"
}

function mpc_test_yao  {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "y"
}

function mpc_test_6  {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "a+y"
}

function mpc_test_7  {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "smart_glp"
}

function mpc_test_8  {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "smart_lp" --num-parts 12 --mut-level 4 --mut-step-size 1 --graph-type 1
}

function mpc_test_9  {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "smart_lp" --num-parts 96 --mut-level 2 --mut-step-size 1 --graph-type 0
}

# mpc_test_7 2 ./examples/C/mpc/benchmarks/histogram/2pc_histogram.c

# mpc_test_7 2 ./examples/C/mpc/benchmarks/cryptonets/cryptonets.c

# mpc_test_8 2 ./examples/C/mpc/benchmarks/biomatch/2pc_biomatch_.c

# mpc_test_8 2 ./examples/C/mpc/benchmarks/kmeans/2pc_kmeans_.c

# mpc_test_8 2 ./examples/C/mpc/benchmarks/mnist/mnist.c

# mpc_test_9 2 ./examples/C/mpc/benchmarks/mnist/mnist28.c

# mpc_test_9 2 ./examples/C/mpc/benchmarks/db/db_join.c

# build div tests
mpc_test_3 2 ./examples/C/mpc/unit_tests/div_tests/2pc_div.c

