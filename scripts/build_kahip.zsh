#!/usr/bin/env zsh

if [[ ! -z ${KAHIP_SOURCE} ]]; then 
    cd ${KAHIP_SOURCE}
    ./compile_withcmake.sh 
else
    echo "Missing KAHIP_SOURCE environment variable."
fi