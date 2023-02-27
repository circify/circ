#!/usr/bin/env zsh

if [[ ! -z ${KAHIP_SOURCE} ]]; then 
    cd ${KAHIP_SOURCE}
    ./compile_withcmake.sh -DCMAKE_BUILD_TYPE=Release -DPARHIP=off
else
    echo "Missing KAHIP_SOURCE environment variable."
fi