#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --release --example circ

BIN=./target/release/examples/circ

# Test prove workflow
$BIN examples/C/pf/add.c r1cs --action setup
$BIN --inputs examples/C/pf/inputs/add.c.in examples/C/pf/add.c r1cs --action prove
$BIN examples/C/pf/add.c r1cs --action verify
rm -rf P V pi
