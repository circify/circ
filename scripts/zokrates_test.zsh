#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --release --example circ

BIN=./target/release/examples/circ

function r1cs_test {
    zpath=$1
    time --format='%e seconds %M kB' $BIN $zpath
}

function mpc_test {
    parties=$1
    zpath=$2
    RUST_BACKTRACE=1 time --format='%e seconds %M kB' $BIN -p $parties $zpath
}

r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsAdd.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsOnCurve.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsOrderCheck.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsNegate.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/multiplexer/lookup1bit.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/multiplexer/lookup2bit.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/multiplexer/lookup3bitSigned.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/casts/bool_128_to_u32_4.zok
#r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/pack/u32/pack128.zok
#r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/pack/bool/pack128.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsScalarMult.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/hashes/mimc7/mimc7R20.zok
r1cs_test ./third_party/ZoKrates/zokrates_stdlib/stdlib/hashes/pedersen/512bit.zok

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

# build mpc bitwise tests
mpc_test 2 ./examples/ZoKrates/mpc/bitwise_tests/2pc_bitwise_and.zok
mpc_test 2 ./examples/ZoKrates/mpc/bitwise_tests/2pc_bitwise_or.zok
mpc_test 2 ./examples/ZoKrates/mpc/bitwise_tests/2pc_bitwise_xor.zok

# build mpc boolean tests
mpc_test 2 ./examples/ZoKrates/mpc/boolean_tests/2pc_boolean_and.zok
mpc_test 2 ./examples/ZoKrates/mpc/boolean_tests/2pc_boolean_or.zok
mpc_test 2 ./examples/ZoKrates/mpc/boolean_tests/2pc_boolean_equals.zok

# build mpc misc tests
mpc_test 2 ./examples/ZoKrates/mpc/2pc_millionaire.zok
