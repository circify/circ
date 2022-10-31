#!/usr/bin/env zsh

if [[ ! -z ${ABY_SOURCE} ]]; then 
    cd ${ABY_SOURCE}
    git checkout functions 
    mkdir -p -- build
    cd build
    cmake .. -DABY_BUILD_EXE=On
    make
else
    echo "Missing ABY_SOURCE environment variable."
fi