#!/usr/bin/env zsh

if [[ ! -z ${ABY_SOURCE} ]]; then 
    rm -rf ${ABY_SOURCE}/build 
    rm -rf ${ABY_SOURCE}/src/examples/2pc_* 
    sed '/add_subdirectory.*2pc.*/d' -i ${ABY_SOURCE}/src/examples/CMakeLists.txt 
else 
  echo "Missing ABY_SOURCE environment variable."
fi 