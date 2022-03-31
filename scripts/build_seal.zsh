#!/usr/bin/env zsh

if [[ ! -z ${SEAL_SOURCE} ]]; then 
    mkdir -p -- ${SEAL_SOURCE}/build
    cd ${SEAL_SOURCE}
    cmake --build build
else
    echo "Missing SEAL_SOURCE environment variable."
fi