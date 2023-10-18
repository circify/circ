#!/usr/bin/env zsh

set -ex

# cargo build --release --features lp,r1cs,smt,zok --example circ

MODE=debug # release or debug
BIN=./target/$MODE/examples/circ
ZK_BIN=./target/$MODE/examples/zk

# Test prove workflow, given an example name
function c_pf_test {
    proof_impl=groth16
    ex_name=$1
    $BIN examples/C/r1cs/$ex_name.c r1cs --action setup --proof-impl $proof_impl
    $ZK_BIN --inputs examples/C/r1cs/$ex_name.c.pin --action prove --proof-impl $proof_impl
    $ZK_BIN --inputs examples/C/r1cs/$ex_name.c.vin --action verify --proof-impl $proof_impl
    rm -rf P V pi
}

c_pf_test add
