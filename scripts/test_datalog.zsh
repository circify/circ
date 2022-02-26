#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --example circ

BIN=./target/debug/examples/circ

$BIN --language datalog ./examples/datalog/parse_test/one_rule.pl r1cs --action count || true
$BIN --language datalog ./examples/datalog/inv.pl r1cs --action count || true
$BIN --language datalog ./examples/datalog/call.pl r1cs --action count || true
$BIN --language datalog ./examples/datalog/arr.pl r1cs --action count || true
# Small R1cs b/c too little recursion.
size=$(($BIN --language datalog ./examples/datalog/dumb_hash.pl -r 4 r1cs --action count || true) | egrep "Final R1cs size:" | egrep -o "\\b[0-9]+")
[ "$size" -lt 10 ]

# Big R1cs b/c enough recursion
size=$(($BIN --language datalog ./examples/datalog/dumb_hash.pl -r 5 r1cs --action count || true) | egrep "Final R1cs size:" | egrep -o "\\b[0-9]+")
[ "$size" -gt 250 ]
size=$(($BIN --language datalog ./examples/datalog/dumb_hash.pl -r 10 r1cs --action count || true) | egrep "Final R1cs size:" | egrep -o "\\b[0-9]+")
[ "$size" -gt 250 ]
size=$(($BIN --language datalog ./examples/datalog/dec.pl -r 2 r1cs --action count || true) | egrep "Final R1cs size:" | egrep -o "\\b[0-9]+")
[ "$size" -gt 250 ]

# Test prim-rec test
$BIN --language datalog ./examples/datalog/dec.pl --lint-prim-rec smt

($BIN --language datalog ./examples/datalog/not_dec.pl --lint-prim-rec smt || true) | egrep 'Not prim'
