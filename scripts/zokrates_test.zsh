#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features r1cs,smt,zok --example circ
# cargo build --example circ

MODE=release # debug or release
BIN=./target/$MODE/examples/circ
ZK_BIN=./target/$MODE/examples/zk

case "$OSTYPE" in 
    darwin*)
        alias measure_time="gtime --format='%e seconds %M kB'"
    ;;
    linux*)
        alias measure_time="time --format='%e seconds %M kB'"
    ;;
esac

function r1cs_test {
    zpath=$1
    measure_time $BIN $zpath r1cs --action count
}

# Test prove workflow, given an example name
function pf_test {
    ex_name=$1
    $BIN examples/ZoKrates/pf/$ex_name.zok r1cs --action setup
    $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.pin --action prove
    $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.vin --action verify
    rm -rf P V pi
}

# Test prove workflow with --z-isolate-asserts, given an example name
function pf_test_isolate {
    ex_name=$1
    $BIN --z-isolate-asserts examples/ZoKrates/pf/$ex_name.zok r1cs --action setup
    $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.pin --action prove
    $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.vin --action verify
    rm -rf P V pi
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

pf_test assert
pf_test_isolate isolate_assert
pf_test 3_plus
pf_test xor
pf_test mul
pf_test many_pub
pf_test str_str
pf_test str_arr_str
pf_test arr_str_arr_str
pf_test var_idx_arr_str_arr_str
pf_test mm

scripts/zx_tests/run_tests.sh
