#!/bin/bash
sudo apt-get update
sudo apt-get install -y build-essential
sudo apt-get install -y cmake
sudo apt-get install -y libgmp-dev
sudo apt-get install -y libssl-dev
sudo apt-get install -y libboost-all-dev
sudo apt-get install -y ufw
sudo ufw allow 7766

git clone https://github.com/circify/circ.git
git clone https://github.com/edwjchen/ABY.git

cd ABY && git checkout functions && mkdir build && cd build
cmake .. -DABY_BUILD_EXE=On -DCMAKE_BUILD_TYPE=Release
make 

cd ~/circ && git checkout mpc_aws