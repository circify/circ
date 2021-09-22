#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --example circ

BIN=./target/debug/examples/circ

$BIN --lang datalog ./examples/datalog/parse_test/one_rule.pl || true
$BIN --lang datalog ./examples/datalog/inv.pl || true
$BIN --lang datalog ./examples/datalog/call.pl || true
$BIN --lang datalog ./examples/datalog/arr.pl || true
