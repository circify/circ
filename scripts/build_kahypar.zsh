#!/usr/bin/env zsh

if [[ ! -z ${KAHYPAR_SOURCE} ]]; then 
    cd ${KAHYPAR_SOURCE}
    mkdir -p build && cd build
    cmake .. -DCMAKE_BUILD_TYPE=RELEASE
    make
else
    echo "Missing KAHYPAR_SOURCE environment variable."
fi