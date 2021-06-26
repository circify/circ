#!/usr/bin/env zsh

set -ex

disable -r time

cargo build --release --example circ

BIN=./target/release/examples/circ

function test_path {
    zpath=$1
    time --format='%e seconds %M kB' $BIN $zpath
}

test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsAdd.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsOnCurve.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsOrderCheck.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsNegate.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/multiplexer/lookup1bit.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/multiplexer/lookup2bit.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/multiplexer/lookup3bitSigned.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/casts/bool_128_to_u32_4.zok
#test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/pack/u32/pack128.zok
#test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/utils/pack/bool/pack128.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/ecc/edwardsScalarMult.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/hashes/mimc7/mimc7R20.zok
test_path ./third_party/ZoKrates/zokrates_stdlib/stdlib/hashes/pedersen/512bit.zok

test_path ./examples/ZoKrates/mpc/2pc_mult.zok
test_path ./examples/ZoKrates/mpc/2pc_mult_add_pub.zok

