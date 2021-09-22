#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --example circ

BIN=./target/debug/examples/circ

$BIN --lang datalog ./examples/datalog/parse_test/one_rule.pl || true
$BIN --lang datalog ./examples/datalog/inv.pl || true
$BIN --lang datalog ./examples/datalog/call.pl || true
$BIN --lang datalog ./examples/datalog/arr.pl || true
# Small R1cs b/c too little recursion
($BIN --lang datalog ./examples/datalog/dumb_hash.pl -r 5 || true) | rg "Final R1cs size: 1"
# Big R1cs b/c enough recursion
($BIN --lang datalog ./examples/datalog/dumb_hash.pl -r 6 || true) | rg "Final R1cs size: 306"
($BIN --lang datalog ./examples/datalog/dumb_hash.pl -r 10 || true) | rg "Final R1cs size: 306"
