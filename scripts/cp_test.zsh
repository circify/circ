#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features r1cs,smt,zok --example circ
# cargo build --example circ

MODE=release # debug or release
BIN=./target/$MODE/examples/circ
CP_BIN=./target/$MODE/examples/cp
ZK_BIN=./target/$MODE/examples/zk

# Test prove workflow, given an example name
function com_wit_test {
    ex_name=$1
    init_rand=$(mktemp /tmp/tmp.circ.init_rand.XXXXXXXXXX)
    fin_rand=$(mktemp /tmp/tmp.circ.fin_rand.XXXXXXXXXX)
    init_commit=$(mktemp /tmp/tmp.circ.init_commit.XXXXXXXXXX)
    fin_commit=$(mktemp /tmp/tmp.circ.fin_commit.XXXXXXXXXX)
    $BIN --ram true $ex_name r1cs --action cp-setup --proof-impl mirage
    $CP_BIN --action sample-rand --rands $init_rand
    $CP_BIN --action sample-rand --rands $fin_rand
    $CP_BIN --action commit --inputs $ex_name.array.init --rands $init_rand --commits $init_commit
    $CP_BIN --action commit --inputs $ex_name.array.fin --rands $fin_rand --commits $fin_commit
    $CP_BIN --action prove --inputs $ex_name.pin --rands $init_rand --rands $fin_rand
    $CP_BIN --action verify --inputs $ex_name.vin --commits $init_commit --commits $fin_commit
    rm -rf P V pi
    rm -rf $init_rand $fin_rand $init_commit $fin_commit
}

com_wit_test ./examples/ZoKrates/pf/mem/tiny.zok
