#!/usr/bin/env zsh

time cargo build --example opa_bench

for n in 3 10 30 100 300 1000
do
    time cargo run --example opa_bench -- $n
done
