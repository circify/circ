#!/usr/bin/env zsh

set -ex

disable -r time

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

function r1cs_test_count {
    zpath=$1
    threshold=$2
    o=$($BIN $zpath r1cs --action count)
    n_constraints=$(echo $o | grep 'Final R1cs size:' | grep -Eo '\b[0-9]+\b')
    [[ $n_constraints -lt $threshold ]] || (echo "Got $n_constraints, expected < $threshold" && exit 1)
}

# Test prove workflow, given an example name
# examples that don't need modulus change
function pf_test {
    ex_name=$1
    $BIN examples/ZoKrates/pf/$ex_name.zok r1cs --action spartansetup
    $ZK_BIN --pin examples/ZoKrates/pf/$ex_name.zok.pin --vin examples/ZoKrates/pf/$ex_name.zok.vin --action spartan
    rm -rf P V pi
}

# Test prove workflow with --z-isolate-asserts, given an example name
function spartan_test_isolate {
    ex_name=$1
    $BIN --z-isolate-asserts examples/ZoKrates/spartan/$ex_name.zok r1cs --action spartansetup
    $ZK_BIN --pin examples/ZoKrates/spartan/$ex_name.zok.pin --vin examples/ZoKrates/spartan/$ex_name.zok.vin --action spartan
    rm -rf P V pi
}

# Test prove workflow, given an example name
function spartan_test {
    ex_name=$1
    $BIN examples/ZoKrates/spartan/$ex_name.zok r1cs --action spartansetup
    $ZK_BIN --pin examples/ZoKrates/spartan/$ex_name.zok.pin --vin examples/ZoKrates/spartan/$ex_name.zok.vin --action spartan
    rm -rf P V pi
}

r1cs_test_count ./examples/ZoKrates/pf/mm4_cond.zok 120
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

spartan_test assert
spartan_test_isolate isolate_assert
pf_test 3_plus
pf_test xor
spartan_test mul
pf_test many_pub
spartan_test str_str
spartan_test str_arr_str
spartan_test arr_str_arr_str
spartan_test var_idx_arr_str_arr_str
spartan_test mm

