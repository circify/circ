#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --release --example circ
#cargo build --example circ

#BIN=./target/debug/examples/circ
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
    zpath=$1
    measure_time $BIN $zpath r1cs --action count
}

# Test prove workflow, given an example name
function pf_test {
    ex_name=$1
    $BIN examples/ZoKrates/pf/$ex_name.zok r1cs --action setup
    $BIN --inputs examples/ZoKrates/pf/$ex_name.zok.in examples/ZoKrates/pf/$ex_name.zok r1cs --action prove
    $BIN examples/ZoKrates/pf/$ex_name.zok r1cs --instance examples/ZoKrates/pf/$ex_name.zok.x --action verify
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

pf_test 3_plus
pf_test xor
pf_test mul
pf_test many_pub
pf_test str_str
pf_test str_arr_str
pf_test arr_str_arr_str
pf_test var_idx_arr_str_arr_str
pf_test mm
