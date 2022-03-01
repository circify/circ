#!/usr/bin/env zsh

set -ex

disable -r time

# cargo build --release --features lp,smt,zok --example circ

BIN=./target/release/examples/circ

case "$OSTYPE" in 
    darwin*)
        alias measure_time="gtime --format='%e seconds %M kB'"
    ;;
    linux*)
        alias measure_time="time --format='%e seconds %M kB'"
    ;;
esac

function ilp_test {
    zpath=$1
    expected_max=$2
    max=$($BIN $zpath ilp | grep 'Max va'  | awk '{ print $3 }')
    if [[ $max == $expected_max ]]
    then
        echo "pass: $zpath"
    else
        echo "fail: $zpath"
        echo "expected max:  $expected_max"
        echo "got max:  $max"
        exit 1
    fi
}

ilp_test examples/ZoKrates/opt/3_plus_opt.zok 255
ilp_test examples/ZoKrates/opt/id_opt.zok 255
# crashes in solver
#ilp_test examples/ZoKrates/opt/mult_opt.zok
ilp_test examples/ZoKrates/opt/plus_3_opt.zok 255
ilp_test examples/ZoKrates/opt/times_2_opt.zok 254
ilp_test examples/ZoKrates/opt/times_3_opt.zok 255
ilp_test examples/ZoKrates/opt/log.zok 255
ilp_test examples/ZoKrates/opt/log16.zok 65535
