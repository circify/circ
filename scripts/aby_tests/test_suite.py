arithmetic_tests = [
    [
        "Add two numbers",
        "./third_party/ABY/build/bin/2pc_add",
        "./examples/test_inputs/mpc/add.txt",
    ], 
    [
        "Subtract two numbers",
        "./third_party/ABY/build/bin/2pc_sub",
        "./examples/test_inputs/mpc/sub_1.txt",
    ], 
    [
        "Subtract two numbers, negative -1 == 4294967295 because u32",
        "./third_party/ABY/build/bin/2pc_sub",
        "./examples/test_inputs/mpc/sub_2.txt",
    ],
    [
        "Multiply two numbers - 1",
        "./third_party/ABY/build/bin/2pc_mult",
        "./examples/test_inputs/mpc/mult_1.txt",
    ], 
    [
        "Multiply two numbers - 2",
        "./third_party/ABY/build/bin/2pc_mult",
        "./examples/test_inputs/mpc/mult_2.txt",
    ], 
    [
        "Multiply two numbers - 3",
        "./third_party/ABY/build/bin/2pc_mult",
        "./examples/test_inputs/mpc/mult_3.txt",
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value",
        "./third_party/ABY/build/bin/2pc_mult_add_pub",
        "./examples/test_inputs/mpc/mult_add_pub_1.txt",
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value, check only server side public value is added",
        "./third_party/ABY/build/bin/2pc_mult_add_pub",
        "./examples/test_inputs/mpc/mult_add_pub_2.txt",
    ], 
]

mod_tests = [
    [
        "Mod two numbers - 1",
        "./third_party/ABY/build/bin/2pc_mod",
        "./examples/test_inputs/mpc/mod_1.txt",
    ], 
    [
        "Mod two numbers - 2",
        "./third_party/ABY/build/bin/2pc_mod",
        "./examples/test_inputs/mpc/mod_2.txt",
    ], 
    [
        "Mod two numbers - 3",
        "./third_party/ABY/build/bin/2pc_mod",
        "./examples/test_inputs/mpc/mod_3.txt",
    ], 
]

unsigned_arithmetic_tests = [
     [
        "Add two unsigned numbers",
        "./third_party/ABY/build/bin/2pc_add_unsigned",
        "./examples/test_inputs/mpc/add.txt",
    ], 
]

arithmetic_boolean_tests = [
    [
        "Test two numbers are equal - 1",
        "./third_party/ABY/build/bin/2pc_int_equals",
        "./examples/test_inputs/mpc/eq_1.txt",
    ],
    [
        "Test two numbers are equal - 2",
        "./third_party/ABY/build/bin/2pc_int_equals",
        "./examples/test_inputs/mpc/eq_2.txt",
    ], 
    [
        "Test int > int - 1",
        "./third_party/ABY/build/bin/2pc_int_greater_than",
         "./examples/test_inputs/mpc/gt_1.txt",
    ], 
    [
        "Test int > int - 2",
        "./third_party/ABY/build/bin/2pc_int_greater_than",
         "./examples/test_inputs/mpc/gt_2.txt",
    ], 
    [
        "Test int > int - 3",
        "./third_party/ABY/build/bin/2pc_int_greater_than",
        "./examples/test_inputs/mpc/gt_3.txt",
    ], 
    [
        "Test int >= int - 1",
        "./third_party/ABY/build/bin/2pc_int_greater_equals",
        "./examples/test_inputs/mpc/ge_1.txt",
    ], 
    [
        "Test int >= int - 2",
        "./third_party/ABY/build/bin/2pc_int_greater_equals",
        "./examples/test_inputs/mpc/ge_2.txt",
    ], 
    [
        "Test int >= int - 3",
        "./third_party/ABY/build/bin/2pc_int_greater_equals",
        "./examples/test_inputs/mpc/ge_3.txt",
    ],
    [
        "Test int < int - 1",
        "./third_party/ABY/build/bin/2pc_int_less_than",
        "./examples/test_inputs/mpc/lt_1.txt",
    ], 
    [
        "Test int < int - 2",
        "./third_party/ABY/build/bin/2pc_int_less_than",
        "./examples/test_inputs/mpc/lt_2.txt",
    ], 
    [
        "Test int < int - 3",
        "./third_party/ABY/build/bin/2pc_int_less_than",
        "./examples/test_inputs/mpc/lt_3.txt",
    ], 
    [
        "Test int <= int - 1",
        "./third_party/ABY/build/bin/2pc_int_less_equals",
        "./examples/test_inputs/mpc/le_1.txt",
    ], 
    [
        "Test int <= int - 2",
        "./third_party/ABY/build/bin/2pc_int_less_equals",
        "./examples/test_inputs/mpc/le_2.txt",
    ], 
    [
        "Test int <= int - 3",
        "./third_party/ABY/build/bin/2pc_int_less_equals",
        "./examples/test_inputs/mpc/le_3.txt",
    ],
]

nary_arithmetic_tests = [
    [
        "Test a + b + c",
        "./third_party/ABY/build/bin/2pc_nary_arithmetic_add",
        "./examples/test_inputs/mpc/nary_add.txt",
    ],
]

bitwise_tests = [
    [
        "Bitwise & - 1",
        "./third_party/ABY/build/bin/2pc_bitwise_and",
        "./examples/test_inputs/mpc/and_1.txt",
    ],
    [
        "Bitwise & - 2",
        "./third_party/ABY/build/bin/2pc_bitwise_and",
        "./examples/test_inputs/mpc/and_2.txt",
    ],
    [
        "Bitwise & - 3",
        "./third_party/ABY/build/bin/2pc_bitwise_and",
        "./examples/test_inputs/mpc/and_3.txt",
    ],
    [
        "Bitwise & - 4",
        "./third_party/ABY/build/bin/2pc_bitwise_and",
        "./examples/test_inputs/mpc/and_4.txt",
    ],
    [
        "Bitwise | - 1",
        "./third_party/ABY/build/bin/2pc_bitwise_or",
        "./examples/test_inputs/mpc/or_1.txt",
    ],
    [
        "Bitwise | - 2",
        "./third_party/ABY/build/bin/2pc_bitwise_or",
        "./examples/test_inputs/mpc/or_2.txt",
    ],
    [
        "Bitwise | - 3",
        "./third_party/ABY/build/bin/2pc_bitwise_or",
        "./examples/test_inputs/mpc/or_3.txt",
    ],
    [
        "Bitwise | - 4",
        "./third_party/ABY/build/bin/2pc_bitwise_or",
        "./examples/test_inputs/mpc/or_4.txt",
    ],
        [
        "Bitwise ^ - 1",
        "./third_party/ABY/build/bin/2pc_bitwise_xor",
        "./examples/test_inputs/mpc/xor_1.txt",

    ],
    [
        "Bitwise ^ - 2",
        "./third_party/ABY/build/bin/2pc_bitwise_xor",
        "./examples/test_inputs/mpc/xor_2.txt",
    ],
    [
        "Bitwise ^ - 3",
        "./third_party/ABY/build/bin/2pc_bitwise_xor",
        "./examples/test_inputs/mpc/xor_3.txt",
    ],
    [
        "Bitwise ^ - 4",
        "./third_party/ABY/build/bin/2pc_bitwise_xor",
        "./examples/test_inputs/mpc/xor_4.txt",
    ],
]

boolean_tests = [
    [
        "Boolean && - 1",
        "./third_party/ABY/build/bin/2pc_boolean_and",
        "./examples/test_inputs/mpc/and_1.txt",
    ],
    [
        "Boolean && - 2",
        "./third_party/ABY/build/bin/2pc_boolean_and",
        "./examples/test_inputs/mpc/and_2.txt",
    ],
    [
        "Boolean && - 3",
        "./third_party/ABY/build/bin/2pc_boolean_and",
        "./examples/test_inputs/mpc/and_3.txt",
    ],
    [
        "Boolean && - 4",
        "./third_party/ABY/build/bin/2pc_boolean_and",
        "./examples/test_inputs/mpc/and_4.txt",
    ],
    [
        "Boolean || - 1",
        "./third_party/ABY/build/bin/2pc_boolean_or",
        "./examples/test_inputs/mpc/or_1.txt",
    ],
    [
        "Boolean || - 2",
        "./third_party/ABY/build/bin/2pc_boolean_or",
        "./examples/test_inputs/mpc/or_2.txt",

    ],
    [
        "Boolean || - 3",
        "./third_party/ABY/build/bin/2pc_boolean_or",
        "./examples/test_inputs/mpc/or_3.txt",

    ],
    [
        "Boolean || - 4",
        "./third_party/ABY/build/bin/2pc_boolean_or",
        "./examples/test_inputs/mpc/or_4.txt",
    ],
    [
        "Boolean == - 1",
        "./third_party/ABY/build/bin/2pc_boolean_equals",
        "./examples/test_inputs/mpc/eq_1.txt",
    ],
    [
        "Boolean == - 2",
        "./third_party/ABY/build/bin/2pc_boolean_equals",
        "./examples/test_inputs/mpc/eq_2.txt",
    ],
]

nary_boolean_tests = [
    [
        "Test a & b & c",
        "./third_party/ABY/build/bin/2pc_nary_boolean_and",
        "./examples/test_inputs/mpc/nary_and.txt",
    ],
]


const_arith_tests = [
    [
        "Test add client int + server int to const value",
        "./third_party/ABY/build/bin/2pc_const_arith",
        "./examples/test_inputs/mpc/const_add.txt",
    ], 
]

const_bool_tests = [
    [
        "Test server value == const value - 1",
        "./third_party/ABY/build/bin/2pc_const_bool",
        "./examples/test_inputs/mpc/const_eq_1.txt",
    ], 
    [
        "Test server value == const value - 2",
        "./third_party/ABY/build/bin/2pc_const_bool",
        "./examples/test_inputs/mpc/const_eq_2.txt",
    ], 
]

ite_tests = [
    [
        "Test ite ret bool - 1",
        "./third_party/ABY/build/bin/2pc_ite_ret_bool",
        "./examples/test_inputs/mpc/ite_1.txt",
    ],
    [
        "Test ite ret bool - 2",
        "./third_party/ABY/build/bin/2pc_ite_ret_bool",
        "./examples/test_inputs/mpc/ite_2.txt",
    ],
    [
        "Test ite ret int - 1",
        "./third_party/ABY/build/bin/2pc_ite_ret_int",
        "./examples/test_inputs/mpc/ite_1.txt",
    ],
    [
        "Test ite ret int - 2",
        "./third_party/ABY/build/bin/2pc_ite_ret_int",
        "./examples/test_inputs/mpc/ite_2.txt",
    ],
    [
        "Test ite only if - 1",
        "./third_party/ABY/build/bin/2pc_ite_only_if",
        "./examples/test_inputs/mpc/ite_1.txt",
    ],
    [
        "Test ite only if - 2",
        "./third_party/ABY/build/bin/2pc_ite_only_if",
        "./examples/test_inputs/mpc/ite_2.txt",
    ],
]

array_tests = [
    [
        "Array sum test",
        "./third_party/ABY/build/bin/2pc_array_sum",
        "./examples/test_inputs/mpc/add.txt",
    ], 
    [
        "Array index test",
        "./third_party/ABY/build/bin/2pc_array_index",
        "./examples/test_inputs/mpc/add.txt",
    ], 
    [
        "Array index test 2",
        "./third_party/ABY/build/bin/2pc_array_index_2",
        "./examples/test_inputs/mpc/index.txt",
    ], 
]

c_array_tests = [
    [
        "C array test",
        "./third_party/ABY/build/bin/2pc_array",
        "./examples/test_inputs/mpc/array.txt",
    ], 
    [
        "C array test 1",
        "./third_party/ABY/build/bin/2pc_array_1",
        "./examples/test_inputs/mpc/array_1.txt",
    ], 
    [
        "C array test 2",
        "./third_party/ABY/build/bin/2pc_array_2",
        "./examples/test_inputs/mpc/array_2.txt",
    ], 
    [
        "C array test 3",
        "./third_party/ABY/build/bin/2pc_array_3",
        "./examples/test_inputs/mpc/array_3.txt",
    ], 
    [
        "C array test 4",
        "./third_party/ABY/build/bin/2pc_array_sum_c",
        "./examples/test_inputs/mpc/array_4.txt",
    ], 
]

loop_tests = [
    [
        "Loop sum const - 1",
        "./third_party/ABY/build/bin/2pc_loop_sum",
        "./examples/test_inputs/mpc/loop_1.txt",
    ], 
    [
        "Loop sum const - 2",
        "./third_party/ABY/build/bin/2pc_loop_sum",
        "./examples/test_inputs/mpc/loop_2.txt",
    ],
]

function_tests = [
    [
        "Sum() two numbers - 1",
        "./third_party/ABY/build/bin/2pc_function_sum",
        "./examples/test_inputs/mpc/add.txt",
    ], 
]

shift_tests = [
     [
        "Left Shift a by 1 - 1",
        "./third_party/ABY/build/bin/2pc_lhs",
        "./examples/test_inputs/mpc/lsh_1.txt",
    ], 
    [
        "Left Shift a by 1 - 2",
        "./third_party/ABY/build/bin/2pc_lhs",
        "./examples/test_inputs/mpc/lsh_2.txt",
    ], 
    [
        "Left Shift a by 1 - 3",
        "./third_party/ABY/build/bin/2pc_lhs",
        "./examples/test_inputs/mpc/lsh_3.txt",
    ], 
    [
        "Right Shift a by 1 - 1",
        "./third_party/ABY/build/bin/2pc_rhs",
        "./examples/test_inputs/mpc/rsh_1.txt",
    ], 
    [
        "Right Shift a by 1 - 2",
        "./third_party/ABY/build/bin/2pc_rhs",
        "./examples/test_inputs/mpc/rsh_2.txt",
    ], 
]


div_tests = [
    [
        "Divide a by 1",
        "./third_party/ABY/build/bin/2pc_div",
        "./examples/test_inputs/mpc/div_1.txt",
    ], 
    [
        "Divide a by b - 1",
        "./third_party/ABY/build/bin/2pc_div",
        "./examples/test_inputs/mpc/div_2.txt",
    ], 
    [
        "Divide a by b - 2",
        "./third_party/ABY/build/bin/2pc_div",
        "./examples/test_inputs/mpc/div_3.txt",
    ], 
    [
        "Divide a by b - 3",
        "./third_party/ABY/build/bin/2pc_div",
        "./examples/test_inputs/mpc/div_4.txt",
    ], 
]

misc_tests = [
    [
        "Millionaire's problem: server has more money than client",
        "./third_party/ABY/build/bin/2pc_millionaires",
        "./examples/test_inputs/mpc/lt_1.txt",
    ], 
    [
        "Millionaire's problem: server has equal money to client",
        "./third_party/ABY/build/bin/2pc_millionaires",
        "./examples/test_inputs/mpc/lt_2.txt",
    ], 
    [
        "Millionaire's problem: server has less money than client",
        "./third_party/ABY/build/bin/2pc_millionaires",
        "./examples/test_inputs/mpc/lt_3.txt",
    ], 
]

kmeans_tests = [
    [
        "kmeans",
        "./third_party/ABY/build/bin/2pc_kmeans",
        "./examples/test_inputs/mpc/kmeans.txt",
    ],     
]

biomatch_tests = [
    [
        "biomatch - 1",
        "./third_party/ABY/build/bin/2pc_biomatch",
        "./examples/test_inputs/mpc/biomatch_1.txt",
    ],   
    [
        "biomatch - 2",
        "./third_party/ABY/build/bin/2pc_biomatch",
        "./examples/test_inputs/mpc/biomatch_2.txt",
    ],   
]

# ilp_benchmark_tests = [
#     [
#         "ilp bench - array sum 1",
#         1000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_1",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],     
#     [
#         "ilp bench - array sum 2",
#         2000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_2",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],   
#     [
#         "ilp bench - array sum 3",
#         3000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_3",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],   
#     [
#         "ilp bench - array sum 4",
#         4000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_4",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],   
#     [
#         "ilp bench - array sum 5",
#         5000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_5",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],   
#     [
#         "ilp bench - array sum 6",
#         6000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_6",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],  
#     [
#         "ilp bench - array sum 7",
#         7000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_7",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],  
#         [
#         "ilp bench - array sum 8",
#         8000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_8",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],  
#         [
#         "ilp bench - array sum 9",
#         9000,
#         "./third_party/ABY/build/bin/2pc_ilp_bench_9",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],  
# ]