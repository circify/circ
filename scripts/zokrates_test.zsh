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

function r1cs_test_count {
    zpath=$1
    threshold=$2
    circoptions=$3
    setopt SH_WORD_SPLIT
    o=$($BIN $circoptions $zpath r1cs --action count)
    unsetopt SH_WORD_SPLIT
    n_constraints=$(echo $o | grep 'Final R1cs size:' | grep -Eo '\b[0-9]+\b')
    [[ $n_constraints -lt $threshold ]] || (echo "Got $n_constraints, expected < $threshold" && exit 1)
}

# Test prove workflow, given an example name
function pf_test {
    for proof_impl in groth16 mirage
    do
        ex_name=$1
        $BIN examples/ZoKrates/pf/$ex_name.zok r1cs --action setup --proof-impl $proof_impl
        $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.pin --action prove --proof-impl $proof_impl
        $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.vin --action verify --proof-impl $proof_impl
        rm -rf P V pi
    done
}

# Test setup + prove, given an example name (does not test verification)
function pf_test_only_pf {
    circoptions=$2
    for proof_impl in mirage
    do
        ex_name=$1
        setopt SH_WORD_SPLIT
        $BIN $circoptions examples/ZoKrates/pf/$ex_name.zok r1cs --action setup --proof-impl $proof_impl
        unsetopt SH_WORD_SPLIT
        $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.pin --action prove --proof-impl $proof_impl
        rm -rf P V pi
    done
}

# Test prove workflow with --z-isolate-asserts, given an example name
function pf_test_isolate {
    for proof_impl in groth16 mirage
    do
        ex_name=$1
        $BIN --zsharp-isolate-asserts true examples/ZoKrates/pf/$ex_name.zok r1cs --action setup --proof-impl $proof_impl
        $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.pin --action prove --proof-impl $proof_impl
        $ZK_BIN --inputs examples/ZoKrates/pf/$ex_name.zok.vin --action verify --proof-impl $proof_impl
        rm -rf P V pi
    done
}

r1cs_test_count ./examples/ZoKrates/pf/mm4_cond.zok 120
r1cs_test_count ./examples/ZoKrates/pf/fits_in_bits.zok 4500 "--ir-fits-in-bits-ip true --ram true"
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

pf_test_only_pf sha_temp1
pf_test_only_pf sha_rot
pf_test_only_pf maj
pf_test_only_pf sha_temp2
pf_test_only_pf fits_in_bits_tiny "--ir-fits-in-bits-ip true --ram true"
#pf_test_only_pf test_sha256

pf_test assert
pf_test assert2
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
pf_test unused_var

scripts/zx_tests/run_tests.sh
