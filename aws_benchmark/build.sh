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
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc"
}

function mpc_test_2  {
    parties=$1
    cpath=$2
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model "hycc" --selection-scheme "a+b"
}

# build hycc benchmarks
mpc_test 2 ./examples/C/mpc/benchmarks/biomatch/2pc_biomatch.c
mpc_test 2 ./examples/C/mpc/benchmarks/biomatch/biomatch.c
mpc_test 2 ./examples/C/mpc/benchmarks/kmeans/2pc_kmeans_.c
mpc_test 2 ./examples/C/mpc/benchmarks/gauss/2pc_gauss_inline.c
mpc_test 2 ./examples/C/mpc/benchmarks/db/db_join.c
mpc_test 2 ./examples/C/mpc/benchmarks/db/db_join2.c
mpc_test 2 ./examples/C/mpc/benchmarks/db/db_merge.c
mpc_test 2 ./examples/C/mpc/benchmarks/mnist/mnist.c
mpc_test_2 2 ./examples/C/mpc/benchmarks/cryptonets/cryptonets.c

# build OPA benchmarks
mpc_test_2 2 ./examples/C/mpc/benchmarks/histogram/histogram.c