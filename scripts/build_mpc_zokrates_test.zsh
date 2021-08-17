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

function mpc_test {
    parties=$1
    zpath=$2
    RUST_BACKTRACE=1 measure_time $BIN -p $parties $zpath
}

# build mpc arithmetic tests
mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_add.zok
mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_sub.zok
mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_mult.zok
mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_mult_add_pub.zok

mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_int_equals.zok
mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_int_greater_than.zok
mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_int_greater_equals.zok
mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_int_less_than.zok
mpc_test 2 ./examples/ZoKrates/mpc/arithmetic_tests/2pc_int_less_equals.zok

# build mpc nary arithmetic tests
mpc_test 2 ./examples/ZoKrates/mpc/nary_arithmetic_tests/2pc_nary_arithmetic_add.zok

# build mpc bitwise tests
mpc_test 2 ./examples/ZoKrates/mpc/bitwise_tests/2pc_bitwise_and.zok
mpc_test 2 ./examples/ZoKrates/mpc/bitwise_tests/2pc_bitwise_or.zok
mpc_test 2 ./examples/ZoKrates/mpc/bitwise_tests/2pc_bitwise_xor.zok

# build mpc boolean tests
mpc_test 2 ./examples/ZoKrates/mpc/boolean_tests/2pc_boolean_and.zok
mpc_test 2 ./examples/ZoKrates/mpc/boolean_tests/2pc_boolean_or.zok
mpc_test 2 ./examples/ZoKrates/mpc/boolean_tests/2pc_boolean_equals.zok

# build mpc nary boolean tests
mpc_test 2 ./examples/ZoKrates/mpc/nary_boolean_tests/2pc_nary_boolean_and.zok

# build mpc const tests
mpc_test 2 ./examples/ZoKrates/mpc/const_tests/2pc_const_arith.zok
mpc_test 2 ./examples/ZoKrates/mpc/const_tests/2pc_const_bool.zok

# build mpc misc tests
mpc_test 2 ./examples/ZoKrates/mpc/2pc_millionaire.zok
