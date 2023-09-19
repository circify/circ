#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features r1cs,smt,zok --example circ
# cargo build --features "zok smt bellman" --example circ --example zk

MODE=release # debug or release
BIN=./target/$MODE/examples/circ
ZK_BIN=./target/$MODE/examples/zk

# Test prove workflow, given an example name
function ram_test {
    proof_impl=$2
    ex_name=$1
    rm -rf P V pi
    $BIN --ram true $=3 $ex_name r1cs --action setup --proof-impl $proof_impl
    $ZK_BIN --inputs $ex_name.pin --action prove --proof-impl $proof_impl
    $ZK_BIN --inputs $ex_name.vin --action verify --proof-impl $proof_impl
    rm -rf P V pi
}

ram_test ./examples/ZoKrates/pf/mem/two_level_ptr.zok groth16 "--ram-permutation waksman --ram-index sort --ram-range bit-split"
ram_test ./examples/ZoKrates/pf/mem/volatile.zok groth16 "--ram-permutation waksman --ram-index sort --ram-range bit-split"
ram_test ./examples/ZoKrates/pf/mem/volatile_struct.zok groth16 "--ram-permutation waksman --ram-index sort --ram-range bit-split"
ram_test ./examples/ZoKrates/pf/mem/two_level_ptr.zok mirage ""
ram_test ./examples/ZoKrates/pf/mem/volatile.zok mirage ""
ram_test ./examples/ZoKrates/pf/mem/volatile_struct.zok mirage ""

