#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features c --example circ 

BIN=./target/release/examples/circ
export CARGO_MANIFEST_DIR=$(pwd)

case "$OSTYPE" in 
    darwin*)
        alias measure_time="gtime --format='LOG: compile time: %e seconds %M kB'"
    ;;
    linux*)
        alias measure_time="time --format='LOG: compile time: %e seconds %M kB'"
    ;;
esac

function mpc_test {
    parties=$1
    cpath=$2
    cm=$3
    ss=$4
    RUST_BACKTRACE=1 measure_time $BIN --parties $parties $cpath mpc --cost-model $cm --selection-scheme $ss
}

# build hycc benchmarks
mpc_test 2 ./examples/C/mpc/benchmarks/biomatch/2pc_biomatch.c $1 $2
mpc_test 2 ./examples/C/mpc/benchmarks/biomatch/biomatch.c $1 $2
mpc_test 2 ./examples/C/mpc/benchmarks/kmeans/2pc_kmeans_.c $1 $2
mpc_test 2 ./examples/C/mpc/benchmarks/gauss/2pc_gauss_inline.c $1 $2
mpc_test 2 ./examples/C/mpc/benchmarks/db/db_join.c $1 $2
mpc_test 2 ./examples/C/mpc/benchmarks/db/db_join2.c $1 $2
mpc_test 2 ./examples/C/mpc/benchmarks/db/db_merge.c $1 $2
mpc_test 2 ./examples/C/mpc/benchmarks/mnist/mnist.c $1 $2
mpc_test_2 2 ./examples/C/mpc/benchmarks/cryptonets/cryptonets.c $1 $2

# build OPA benchmarks
mpc_test_2 2 ./examples/C/mpc/benchmarks/histogram/histogram.c $1 $2
