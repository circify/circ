#!/usr/bin/env zsh

if [[ ! -z ${ABY_SOURCE} ]]; then 
    mkdir -p -- ${ABY_SOURCE}/build
    cd ${ABY_SOURCE}/build
    cmake .. -DABY_BUILD_EXE=On
    make
else
    echo "Missing ABY_SOURCE environment variable."
fi