#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features r1cs,smt,zok --example circ
# cargo build --features "zok smt bellman" --example circ --example zk

MODE=release
MODE=debug
BIN=./target/$MODE/examples/circ
ZK_BIN=./target/$MODE/examples/zk

# Test prove workflow, given an example name
function ram_test {
    proof_impl=$2
    ex_name=$1
    rm -rf P V pi
    $BIN $=3 $ex_name r1cs --action setup --proof-impl $proof_impl
    $ZK_BIN --inputs $ex_name.pin --action prove --proof-impl $proof_impl
    $ZK_BIN --inputs $ex_name.vin --action verify --proof-impl $proof_impl
    rm -rf P V pi
}

# Test for how many transcripts are extracted
function transcript_count_test {
    ex_name=$1
    ex_num=$2
    rm -rf P V pi
    found_num=$(RUST_LOG=circ::ir::opt::mem=debug $BIN $ex_name r1cs --action count |& grep -Eo 'Found [0-9]* transcripts' | grep -Eo '\b[0-9]+\b')
    if [[ ! $ex_num == $found_num ]]
    then
        echo "expected $ex_num transcripts;\n  found $found_num transcripts"
        exit 2
    fi
}

# Test for whether a particular type of transcript is found
function transcript_type_test {
    ex_name=$1
    ex_type=$2
    rm -rf P V pi
    output=$(RUST_LOG=circ::ir::opt::mem=debug $BIN $ex_name r1cs --action count |& cat)
    echo $output
    if (echo $output |& grep "Checking $ex_type") then;
    else
        echo "Did not find a transcript of type $ex_type"
        exit 2
    fi
}

function cs_count_test {
    ex_name=$1
    cs_upper_bound=$2
    rm -rf P V pi
    output=$($BIN $ex_name r1cs --action count |& cat)
    n_constraints=$(echo "$output" | grep 'Final R1cs size:' | grep -Eo '\b[0-9]+\b')
    [[ $n_constraints -lt $cs_upper_bound ]] || (echo "Got $n_constraints, expected < $cs_upper_bound" && exit 1)
}

transcript_count_test ./examples/ZoKrates/pf/mem/volatile.zok 1
transcript_count_test ./examples/ZoKrates/pf/mem/two_level_ptr.zok 1
transcript_count_test ./examples/ZoKrates/pf/mem/volatile_struct.zok 1
transcript_count_test ./examples/ZoKrates/pf/mem/arr_of_str.zok 1
transcript_count_test ./examples/ZoKrates/pf/mem/arr_of_str_of_arr.zok 1

transcript_type_test ./examples/ZoKrates/pf/mem/volatile_struct.zok "RAM"
transcript_type_test ./examples/ZoKrates/pf/mem/two_level_ptr.zok "covering ROM"

# A=400; N=20; L=2; expected cost ~= N + A(L+1) = 1220
cs_count_test ./examples/ZoKrates/pf/mem/rom.zok 1230

ram_test ./examples/ZoKrates/pf/mem/two_level_ptr.zok groth16 "--ram-permutation waksman --ram-index sort --ram-range bit-split"
ram_test ./examples/ZoKrates/pf/mem/volatile.zok groth16 "--ram-permutation waksman --ram-index sort --ram-range bit-split"
# waksman is broken for non-scalar array values
# ram_test ./examples/ZoKrates/pf/mem/volatile_struct.zok groth16 "--ram-permutation waksman --ram-index sort --ram-range bit-split"
# waksman is broken for non-scalar array values
# ram_test ./examples/ZoKrates/pf/mem/arr_of_str.zok groth16 "--ram-permutation waksman --ram-index sort --ram-range bit-split"
ram_test ./examples/ZoKrates/pf/mem/two_level_ptr.zok mirage ""
ram_test ./examples/ZoKrates/pf/mem/volatile.zok mirage ""
ram_test ./examples/ZoKrates/pf/mem/volatile_struct.zok mirage ""
ram_test ./examples/ZoKrates/pf/mem/arr_of_str.zok mirage ""
ram_test ./examples/ZoKrates/pf/mem/arr_of_str_of_arr.zok mirage ""

# challenges
ram_test ./examples/ZoKrates/pf/chall/simple.zok mirage ""
ram_test ./examples/ZoKrates/pf/chall/poly_mult.zok mirage ""
