#!/bin/bash 

# biomatch
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/2pc_biomatch_c -t ./circ/scripts/aby_tests/test_inputs/biomatch_1.txt --address $1 -r $2
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/biomatch_c -t ./circ/scripts/aby_tests/test_inputs/biomatch_1.txt --address $1 -r $2

# kmeans 
./ABY/build/bin/aby_interpreter -m mpc -f mpc_test 2 ./circ/scripts/aby_tests/tests/2pc_kmeans__c -t ./circ/scripts/aby_tests/test_inputs/kmeans.txt --address $1 -r $2

# gauss
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/2pc_gauss_inline_c -t ./circ/scripts/aby_tests/test_inputs/gauss.txt --address $1 -r $2

# db
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/db_join_c -t ./circ/scripts/aby_tests/test_inputs/db_join.txt --address $1 -r $2
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/db_join2_c -t ./circ/scripts/aby_tests/test_inputs/join2.txt --address $1 -r $2
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/db_merge_c -t ./circ/scripts/aby_tests/test_inputs/merge.txt --address $1 -r $2

# mnist
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/mnist_c -t ./circ/scripts/aby_tests/test_inputs/mnist_16.txt --address $1 -r $2

# cryptonets 
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/cryptonets_c -t ./circ/scripts/aby_tests/test_inputs/cryptonets_16.txt --address $1 -r $2

# histogram
./ABY/build/bin/aby_interpreter -m mpc -f ./circ/scripts/aby_tests/tests/histogram_c -t ./circ/scripts/aby_tests/test_inputs/histogram.txt --address $1 -r $2