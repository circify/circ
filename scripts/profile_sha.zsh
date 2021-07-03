#!/usr/bin/env zsh

set -ex

cargo flamegraph --help || (echo "Please install the rust 'flamegraph' binary with 'cargo install flamegraph'" && exit 1)

cargo flamegraph --example circ third_party/ZoKrates/zokrates_stdlib/stdlib/hashes/sha256/shaRound.zok
