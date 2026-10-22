#!/usr/bin/env zsh

# Prove and verify the matrix-multiply examples, with the randomized transform
# on and off, and check that a false statement is rejected either way.

set -ex

disable -r time

MODE=release
BIN=./target/$MODE/examples/circ
ZK_BIN=./target/$MODE/examples/zk

# setup/prove/verify one example under one set of compiler flags
function matmul_test {
    ex_name=$1
    shift
    rm -rf P V pi
    $BIN $@ $ex_name r1cs --action setup --proof-impl mirage
    $ZK_BIN --inputs $ex_name.pin --action prove --proof-impl mirage
    $ZK_BIN --inputs $ex_name.vin --action verify --proof-impl mirage
    rm -rf P V pi
}

# the same, but with a corrupted claim: proving may succeed, verifying must not
function matmul_reject_test {
    ex_name=$1
    shift
    rm -rf P V pi bad.pin bad.vin
    # bump the first entry of the claimed product
    sed '0,/^(P\.0\.0 /s//(P.0.0 #f123456789)\n(unused /' $ex_name.pin \
        | grep -v '^(unused' > bad.pin
    sed '0,/^(P\.0\.0 /s//(P.0.0 #f123456789)\n(unused /' $ex_name.vin \
        | grep -v '^(unused' > bad.vin
    $BIN $@ $ex_name r1cs --action setup --proof-impl mirage
    $ZK_BIN --inputs bad.pin --action prove --proof-impl mirage || true
    if $ZK_BIN --inputs bad.vin --action verify --proof-impl mirage; then
        echo "FAILED: verified a false statement ($ex_name $@)"
        exit 1
    fi
    rm -rf P V pi bad.pin bad.vin
}

for ex in ./examples/ZoKrates/pf/matmul/single.zok \
         ./examples/ZoKrates/pf/matmul/chain.zok \
         ./examples/ZoKrates/pf/matmul/sum.zok
do
    # -rand: the verifier recomputes the products
    matmul_test $ex --ir-matmul-ip false
    matmul_reject_test $ex --ir-matmul-ip false
    # default: each product is a prover hint checked at a random vector
    matmul_test $ex --ir-matmul-ip true
    matmul_reject_test $ex --ir-matmul-ip true
    # +share: same, with the coins the transform named alike merged
    matmul_test $ex --ir-matmul-ip true --ir-share-challenges true
    matmul_reject_test $ex --ir-matmul-ip true --ir-share-challenges true
done

echo "matmul tests passed"
