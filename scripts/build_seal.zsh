#!/usr/bin/env zsh

if [[ ! -z ${SEAL_SOURCE} ]]; then 
    cd ${SEAL_SOURCE}
    cmake -S . -B build -DSEAL_BUILD_EXAMPLES=ON
    cmake --build build
else
    echo "Missing SEAL_SOURCE environment variable."
fi