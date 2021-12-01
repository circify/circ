arithmetic_tests = [
    [
        "Add two numbers - 1",
        3,
        "./third_party/ABY/build/bin/2pc_add",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Add two numbers - 2",
        2,
        "./third_party/ABY/build/bin/2pc_add",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Subtract two numbers",
        1,
        "./third_party/ABY/build/bin/2pc_sub",
        {"a": 3, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Subtract two numbers, negative -1 == 4294967295 because u32",
        4294967295,
        "./third_party/ABY/build/bin/2pc_sub",
        {"a": 2, "b": 0},
        {"a": 0, "b": 3},
    ],
    [
        "Multiply two numbers - 1",
        0,
        "./third_party/ABY/build/bin/2pc_mult",
        {"a": 0, "b": 0},
        {"a": 0, "b": 5},
    ], 
        [
        "Multiply two numbers - 2",
        5,
        "./third_party/ABY/build/bin/2pc_mult",
        {"a": 1, "b": 0},
        {"a": 0, "b": 5},
    ], 
        [
        "Multiply two numbers - 3",
        10,
        "./third_party/ABY/build/bin/2pc_mult",
        {"a": 2, "b": 0},
        {"a": 0, "b": 5},
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value",
        42,
        "./third_party/ABY/build/bin/2pc_mult_add_pub",
        {"a": 5, "b": 0, "v": 7},
        {"a": 0, "b": 7, "v": 7},
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value, check only server side public value is added",
        42,
        "./third_party/ABY/build/bin/2pc_mult_add_pub",
        {"a": 5, "b": 0, "v": 7},
        {"a": 0, "b": 7, "v": 0},
    ], 
]

mod_tests = [
    [
        "Mod two numbers - 1",
        0,
        "./third_party/ABY/build/bin/2pc_mod",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Mod two numbers - 2",
        1,
        "./third_party/ABY/build/bin/2pc_mod",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Mod two numbers - 3",
        0,
        "./third_party/ABY/build/bin/2pc_mod",
        {"a": 2, "b": 0},
        {"a": 0, "b": 2},
    ], 
]

unsigned_arithmetic_tests = [
     [
        "Add two unsigned numbers - 1",
        3,
        "./third_party/ABY/build/bin/2pc_add_unsigned",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
]

arithmetic_boolean_tests = [
    [
        "Test two numbers are equal - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_equals",
        {"a": 5, "b": 0},
        {"a": 0, "b": 7},
    ],
    [
        "Test two numbers are equal - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_than",
        {"a": 5, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 2",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_than",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 3",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_than",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 1",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_equals",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 3",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_equals",
        {"a": 6, "b": 0},
        {"a": 0, "b": 7},
    ],
        [
        "Test int < int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_than",
        {"a": 7, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Test int < int - 2",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_than",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int < int - 3",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_than",
        {"a": 2, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int <= int - 1",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 8},
    ], 
    [
        "Test int <= int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int <= int - 3",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_equals",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ],
    [
        "Test int == int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 8},
    ], 
    [
        "Test int == int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_equals",
        {"a": 12, "b": 0},
        {"a": 0, "b": 12},
    ],
]

nary_arithmetic_tests = [
    [
        "Test a + b + c",
        6,
        "./third_party/ABY/build/bin/2pc_nary_arithmetic_add",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 2, "c": 3},
    ],
]

bitwise_tests = [
    [
        "Bitwise & - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise & - 2",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise & - 3",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise & - 4",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_and",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise | - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_or",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise | - 2",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise | - 3",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise | - 4",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
        [
        "Bitwise ^ - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_xor",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise ^ - 2",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_xor",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise ^ - 3",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_xor",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise ^ - 4",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_xor",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
]

boolean_tests = [
    [
        "Boolean && - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean && - 2",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean && - 3",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean && - 4",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_and",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean || - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_or",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean || - 2",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean || - 3",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean || - 4",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean == - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_equals",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean == - 2",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_equals",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
]

nary_boolean_tests = [
    [
        "Test a & b & c - 1",
        0,
        "./third_party/ABY/build/bin/2pc_nary_boolean_and",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 1, "c": 0},
    ],
    [
        "Test a & b & c - 2",
        1,
        "./third_party/ABY/build/bin/2pc_nary_boolean_and",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 1, "c": 1},
    ],
]


const_arith_tests = [
    [
        "Test add client int + server int to const value",
        6,
        "./third_party/ABY/build/bin/2pc_const_arith",
        {"a": 2, "b": 0},
        {"a": 0, "b": 3},
    ], 
]

const_bool_tests = [
 [
        "Test server value == const value - 1",
        0,
        "./third_party/ABY/build/bin/2pc_const_bool",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ], 
    [
        "Test server value == const value - 2",
        1,
        "./third_party/ABY/build/bin/2pc_const_bool",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ], 
]

ite_tests = [
    [
        "Test ite ret bool - 1",
        0,
        "./third_party/ABY/build/bin/2pc_ite_ret_bool",
        {"a": 0, "b": 0, "sel": 1},
        {"a": 0, "b": 1, "sel": 1},
    ],
    [
        "Test ite ret bool - 2",
        1,
        "./third_party/ABY/build/bin/2pc_ite_ret_bool",
        {"a": 0, "b": 0, "sel": 0},
        {"a": 0, "b": 1, "sel": 0},
    ],
        [
        "Test ite ret int - 1",
        32,
        "./third_party/ABY/build/bin/2pc_ite_ret_int",
        {"a": 32, "b": 0, "sel": 1},
        {"a": 0, "b": 45, "sel": 1},
    ],
    [
        "Test ite ret int - 2",
        45,
        "./third_party/ABY/build/bin/2pc_ite_ret_int",
        {"a": 32, "b": 0, "sel": 0},
        {"a": 0, "b": 45, "sel": 0},
    ],
    [
        "Test ite only if - 1",
        32,
        "./third_party/ABY/build/bin/2pc_ite_ret_int",
        {"a": 32, "b": 0, "sel": 1},
        {"a": 0, "b": 45, "sel": 1},
    ],
    [
        "Test ite only if - 2",
        45,
        "./third_party/ABY/build/bin/2pc_ite_ret_int",
        {"a": 32, "b": 0, "sel": 0},
        {"a": 0, "b": 45, "sel": 0},
    ],
]

array_tests = [
    [
        "Array sum test",
        3,
        "./third_party/ABY/build/bin/2pc_array_sum",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Array index test",
        3,
        "./third_party/ABY/build/bin/2pc_array_index",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Array index test 2",
        2,
        "./third_party/ABY/build/bin/2pc_array_index_2",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    # [
    #     "Array ret test",
    #     "2\n1",
    #     "./third_party/ABY/build/bin/2pc_array_ret",
    #     {"a": 2, "b": 0},
    #     {"a": 0, "b": 1},
    # ], 
]

c_array_tests = [
    [
        "C array test",
        2,
        "./third_party/ABY/build/bin/2pc_array",
        {"a": 2, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "C array test 1",
        17,
        "./third_party/ABY/build/bin/2pc_array_1",
        {"a": 10, "b": 0},
        {"a": 0, "b": 3},
    ], 
    [
        "C array test 2",
        17,
        "./third_party/ABY/build/bin/2pc_array_2",
        {"a": 10, "b": 0},
        {"a": 0, "b": 3},
    ], 
    [
        "C array test 3",
        18,
        "./third_party/ABY/build/bin/2pc_array_3",
        {"a": 2, "b": 0},
        {"a": 0, "b": 3},
    ], 
    [
        "C array test 3",
        30,
        "./third_party/ABY/build/bin/2pc_array_sum_c",
        {"a": [1,2,3,4,5], "b": 7},
        {"a": 6, "b": [1,2,3,4,5]},
    ], 
]

loop_tests = [
    [
        "Loop sum const - 1",
        10,
        "./third_party/ABY/build/bin/2pc_loop_sum",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Loop sum const - 2",
        10,
        "./third_party/ABY/build/bin/2pc_loop_sum",
        {"a": 10, "b": 0},
        {"a": 0, "b": 3},
    ],
]

function_tests = [
    [
        "Sum() two numbers - 1",
        3,
        "./third_party/ABY/build/bin/2pc_function_sum",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Sum() two numbers - 2",
        2,
        "./third_party/ABY/build/bin/2pc_function_sum",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 

]

shift_tests = [
     [
        "Left Shift a by 1 - 1",
        20,
        "./third_party/ABY/build/bin/2pc_lhs",
        {"a": 10, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Left Shift a by 1 - 2",
        0,
        "./third_party/ABY/build/bin/2pc_lhs",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Left Shift a by 1 - 3",
        0,
        "./third_party/ABY/build/bin/2pc_lhs",
        {"a": 2147483648, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Right Shift a by 1 - 1",
        10,
        "./third_party/ABY/build/bin/2pc_rhs",
        {"a": 20, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Right Shift a by 1 - 2",
        0,
        "./third_party/ABY/build/bin/2pc_rhs",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
]


div_tests = [
    [
        "Divide a by 1",
        10,
        "./third_party/ABY/build/bin/2pc_div",
        {"a": 10, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Divide a by b - 1",
        5,
        "./third_party/ABY/build/bin/2pc_div",
        {"a": 10, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Divide a by b - 2",
        5,
        "./third_party/ABY/build/bin/2pc_div",
        {"a": 11, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Divide a by b - 3",
        0,
        "./third_party/ABY/build/bin/2pc_div",
        {"a": 49, "b": 0},
        {"a": 0, "b": 50},
    ], 
    [
        "Divide - 2",
        4,
        "./third_party/ABY/build/bin/2pc_div_2",
        {"a": 49, "b": 0},
        {"a": 0, "b": 50},
    ], 
]

misc_tests = [
    [
        "Millionaire's problem: server has more money than client",
        0,
        "./third_party/ABY/build/bin/2pc_millionaire",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Millionaire's problem: server has equal money to client",
        0,
        "./third_party/ABY/build/bin/2pc_millionaire",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Millionaire's problem: server has less money than client",
        1,
        "./third_party/ABY/build/bin/2pc_millionaire",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Conversion problem",
        7,
        "./third_party/ABY/build/bin/2pc_conv",
        {"a": 0, "b": 0},
        {"a": 0, "b": 7},
    ], 
]

kmeans_tests = [
    [
        "kmeans",
        103,
        "./third_party/ABY/build/bin/2pc_kmeans",
        {"a": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], "b": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]},
        {"a": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], "b": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]},
        # {"a": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99], "b": 0},
        # {"a": 0, "b": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99]},
    ],     
]

ilp_benchmark_tests = [
    [
        "ilp bench - array sum 1",
        1000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_1",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],     
    [
        "ilp bench - array sum 2",
        2000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_2",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],   
    [
        "ilp bench - array sum 3",
        3000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_3",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],   
    [
        "ilp bench - array sum 4",
        4000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_4",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],   
    [
        "ilp bench - array sum 5",
        5000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_5",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],   
    [
        "ilp bench - array sum 6",
        6000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_6",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],  
    [
        "ilp bench - array sum 7",
        7000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_7",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],  
        [
        "ilp bench - array sum 8",
        8000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_8",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],  
        [
        "ilp bench - array sum 9",
        9000,
        "./third_party/ABY/build/bin/2pc_ilp_bench_9",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],  

]

millionaires_test = [
    [
        "Millionaire's problem",
        0,
        "./third_party/ABY/build/bin/2pc_millionaires",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
]

# ree_tests = [
#     [
#         "Array sum test 2",
#         6,
#         "./third_party/ABY/build/bin/2pc_array_sum_2",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ], 
# ]
