#!/usr/bin/env zsh

mkdir -p -- third_party/ABY/build
cd third_party/ABY/build
cmake .. -DABY_BUILD_EXE=On
make