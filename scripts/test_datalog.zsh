#!/usr/bin/env zsh

set -ex

disable -r time

BIN=./target/debug/examples/circ

$BIN --language datalog ./examples/datalog/parse_test/one_rule.pl r1cs --action count || true
$BIN --language datalog ./examples/datalog/inv.pl r1cs --action count || true
$BIN --language datalog ./examples/datalog/call.pl r1cs --action count || true
$BIN --language datalog ./examples/datalog/arr.pl r1cs --action count || true
# Small R1cs b/c too little recursion.
size=$(($BIN --language datalog ./examples/datalog/dumb_hash.pl --datalog-rec-limit 4 r1cs --action count || true) |  grep -E "Final R1cs size:" |  grep -E -o "\\b[0-9]+")
[ "$size" -lt 10 ]

# Big R1cs b/c enough recursion
size=$(($BIN --language datalog ./examples/datalog/dumb_hash.pl --datalog-rec-limit 5 r1cs --action count || true) |  grep -E "Final R1cs size:" |  grep -E -o "\\b[0-9]+")
[ "$size" -gt 250 ]
size=$(($BIN --language datalog ./examples/datalog/dumb_hash.pl --datalog-rec-limit 10 r1cs --action count || true) |  grep -E "Final R1cs size:" |  grep -E -o "\\b[0-9]+")
[ "$size" -gt 250 ]
size=$(($BIN --language datalog ./examples/datalog/dec.pl --datalog-rec-limit 2 r1cs --action count || true) |  grep -E "Final R1cs size:" |  grep -E -o "\\b[0-9]+")
[ "$size" -gt 250 ]

# Test prim-rec test
$BIN --language datalog ./examples/datalog/dec.pl --datalog-lint-prim-rec true smt

($BIN --language datalog ./examples/datalog/not_dec.pl --datalog-lint-prim-rec true smt || true) |  grep -E 'Not prim'
