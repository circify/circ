set -xe

cargo build --release --features 'zok r1cs smt' --example zxe --example zxc

ZXC=target/release/examples/zxc
ZXE=target/release/examples/zxe
PROPERTY=examples/ZoKrates/pf/3_plus.zok
PROVER_INPUT=examples/ZoKrates/pf/3_plus.zok.pin
PROVER_DATA=out.pdat
VERIFIER_DATA=out.vdat

# Remove any old data
rm -f $PROVER_DATA $VERIFIER_DATA

$ZXC $PROPERTY
$ZXE $PROVER_DATA --inputs $PROVER_INPUT


