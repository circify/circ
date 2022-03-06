#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features lp,r1cs,smt,zok --example circ

BIN=./target/release/examples/circ

function ilp_test {
    zpath=$1
    expected_max=$2
    # writes to assignment.txt
    max=$($BIN $zpath ilp | grep 'Max va' | awk '{ print $3 }')
    if [[ $max == $expected_max ]]
    then
        $BIN --value-threshold $max $zpath r1cs --action setup
        $BIN --inputs assignment.txt --value-threshold $max $zpath r1cs --action prove
        touch x
        $BIN $zpath r1cs --instance x --action verify
        echo "pass: $zpath"
        rm assignment.txt P V pi x
    else
        echo "fail: $zpath"
        echo "expected max:  $expected_max"
        echo "got max:  $max"
        exit 1
    fi
}

ilp_test examples/ZoKrates/opt/3_plus_opt.zok 255
ilp_test examples/ZoKrates/opt/id_opt.zok 255
ilp_test examples/ZoKrates/opt/plus_3_opt.zok 255
ilp_test examples/ZoKrates/opt/times_2_opt.zok 254
ilp_test examples/ZoKrates/opt/times_3_opt.zok 255
ilp_test examples/ZoKrates/opt/log.zok 255
ilp_test examples/ZoKrates/opt/log16.zok 65535
