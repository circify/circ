#!/usr/bin/env zsh

set -ex

# cargo build --release --features lp,r1cs,smt,zok --example circ

MODE=release # release or debug
BIN=./target/$MODE/examples/circ

function c_smt_test {
    cpath=$1
    expect_counterexample=$2
    $BIN --c-sv-functions --c-assert-no-ub $cpath smt > tmpout || echo failed
    if grep "Counterexample" tmpout
    then
        found_counterexample=yes
    else
        found_counterexample=no
    fi
    if [[ "$expect_counterexample" == "$found_counterexample" ]]
    then
        echo "Test passed: $cpath"
    else
        echo "Test failed: $cpath"
        echo "Expected Counterexample: $expect_counterexample"
        echo "   Found Counterexample: $found_counterexample"
        echo "Output:"
        cat tmpout
        rm tmpout
        exit 1
    fi
    rm tmpout
}
c_smt_test examples/C/smt/assert_assume_fails.c yes
c_smt_test examples/C/smt/assert_assume_ok.c no
c_smt_test examples/C/smt/assert_fails.c yes
c_smt_test examples/C/smt/defined_return.c no
c_smt_test examples/C/smt/shl_fails_1.c yes
c_smt_test examples/C/smt/shl_fails_2.c yes
c_smt_test examples/C/smt/shl_fails_3.c yes
c_smt_test examples/C/smt/shl_fails_4.c yes
c_smt_test examples/C/smt/shl_ok.c no
