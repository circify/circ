import os
ABY_SOURCE = os.getenv('ABY_SOURCE')

arithmetic_tests = [
    [
        "Add two numbers - 1",
        3,
        ABY_SOURCE+"/build/bin/2pc_add",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Add two numbers - 2",
        2,
        ABY_SOURCE+"/build/bin/2pc_add",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Subtract two numbers",
        1,
        ABY_SOURCE+"/build/bin/2pc_sub",
        {"a": 3, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Subtract two numbers, negative -1 == 4294967295 because u32",
        4294967295,
        ABY_SOURCE+"/build/bin/2pc_sub",
        {"a": 2, "b": 0},
        {"a": 0, "b": 3},
    ],
    [
        "Multiply two numbers - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_mult",
        {"a": 0, "b": 0},
        {"a": 0, "b": 5},
    ], 
        [
        "Multiply two numbers - 2",
        5,
        ABY_SOURCE+"/build/bin/2pc_mult",
        {"a": 1, "b": 0},
        {"a": 0, "b": 5},
    ], 
        [
        "Multiply two numbers - 3",
        10,
        ABY_SOURCE+"/build/bin/2pc_mult",
        {"a": 2, "b": 0},
        {"a": 0, "b": 5},
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value",
        42,
        ABY_SOURCE+"/build/bin/2pc_mult_add_pub",
        {"a": 5, "b": 0, "v": 7},
        {"a": 0, "b": 7, "v": 7},
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value, check only server side public value is added",
        42,
        ABY_SOURCE+"/build/bin/2pc_mult_add_pub",
        {"a": 5, "b": 0, "v": 7},
        {"a": 0, "b": 7, "v": 0},
    ], 
]

mod_tests = [
    [
        "Mod two numbers - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_mod",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Mod two numbers - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_mod",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Mod two numbers - 3",
        0,
        ABY_SOURCE+"/build/bin/2pc_mod",
        {"a": 2, "b": 0},
        {"a": 0, "b": 2},
    ], 
]

unsigned_arithmetic_tests = [
     [
        "Add two unsigned numbers - 1",
        3,
        ABY_SOURCE+"/build/bin/2pc_add_unsigned",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
]

arithmetic_boolean_tests = [
    [
        "Test two numbers are equal - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_int_equals",
        {"a": 5, "b": 0},
        {"a": 0, "b": 7},
    ],
    [
        "Test two numbers are equal - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_int_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_int_greater_than",
        {"a": 5, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 2",
        0,
        ABY_SOURCE+"/build/bin/2pc_int_greater_than",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 3",
        1,
        ABY_SOURCE+"/build/bin/2pc_int_greater_than",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 1",
        1,
        ABY_SOURCE+"/build/bin/2pc_int_greater_equals",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_int_greater_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 3",
        0,
        ABY_SOURCE+"/build/bin/2pc_int_greater_equals",
        {"a": 6, "b": 0},
        {"a": 0, "b": 7},
    ],
        [
        "Test int < int - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_int_less_than",
        {"a": 7, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Test int < int - 2",
        0,
        ABY_SOURCE+"/build/bin/2pc_int_less_than",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int < int - 3",
        1,
        ABY_SOURCE+"/build/bin/2pc_int_less_than",
        {"a": 2, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int <= int - 1",
        1,
        ABY_SOURCE+"/build/bin/2pc_int_less_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 8},
    ], 
    [
        "Test int <= int - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_int_less_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int <= int - 3",
        0,
        ABY_SOURCE+"/build/bin/2pc_int_less_equals",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ],
    [
        "Test int == int - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_int_equals",
        {"a": 7, "b": 0},
        {"a": 0, "b": 8},
    ], 
    [
        "Test int == int - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_int_equals",
        {"a": 12, "b": 0},
        {"a": 0, "b": 12},
    ],
]

nary_arithmetic_tests = [
    [
        "Test a + b + c",
        6,
        ABY_SOURCE+"/build/bin/2pc_nary_arithmetic_add",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 2, "c": 3},
    ],
]

bitwise_tests = [
    [
        "Bitwise & - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_bitwise_and",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise & - 2",
        0,
        ABY_SOURCE+"/build/bin/2pc_bitwise_and",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise & - 3",
        0,
        ABY_SOURCE+"/build/bin/2pc_bitwise_and",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise & - 4",
        1,
        ABY_SOURCE+"/build/bin/2pc_bitwise_and",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise | - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_bitwise_or",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise | - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_bitwise_or",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise | - 3",
        1,
        ABY_SOURCE+"/build/bin/2pc_bitwise_or",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise | - 4",
        1,
        ABY_SOURCE+"/build/bin/2pc_bitwise_or",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
        [
        "Bitwise ^ - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_bitwise_xor",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise ^ - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_bitwise_xor",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise ^ - 3",
        1,
        ABY_SOURCE+"/build/bin/2pc_bitwise_xor",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise ^ - 4",
        0,
        ABY_SOURCE+"/build/bin/2pc_bitwise_xor",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
]

boolean_tests = [
    [
        "Boolean && - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_boolean_and",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean && - 2",
        0,
        ABY_SOURCE+"/build/bin/2pc_boolean_and",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean && - 3",
        0,
        ABY_SOURCE+"/build/bin/2pc_boolean_and",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean && - 4",
        1,
        ABY_SOURCE+"/build/bin/2pc_boolean_and",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean || - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_boolean_or",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean || - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_boolean_or",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean || - 3",
        1,
        ABY_SOURCE+"/build/bin/2pc_boolean_or",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean || - 4",
        1,
        ABY_SOURCE+"/build/bin/2pc_boolean_or",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean == - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_boolean_equals",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean == - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_boolean_equals",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
]

nary_boolean_tests = [
    [
        "Test a & b & c - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_nary_boolean_and",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 1, "c": 0},
    ],
    [
        "Test a & b & c - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_nary_boolean_and",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 1, "c": 1},
    ],
]


const_arith_tests = [
    [
        "Test add client int + server int to const value",
        6,
        ABY_SOURCE+"/build/bin/2pc_const_arith",
        {"a": 2, "b": 0},
        {"a": 0, "b": 3},
    ], 
]

const_bool_tests = [
 [
        "Test server value == const value - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_const_bool",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ], 
    [
        "Test server value == const value - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_const_bool",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ], 
]

ite_tests = [
    [
        "Test ite ret bool - 1",
        0,
        ABY_SOURCE+"/build/bin/2pc_ite_ret_bool",
        {"a": 0, "b": 0, "sel": 1},
        {"a": 0, "b": 1, "sel": 1},
    ],
    [
        "Test ite ret bool - 2",
        1,
        ABY_SOURCE+"/build/bin/2pc_ite_ret_bool",
        {"a": 0, "b": 0, "sel": 0},
        {"a": 0, "b": 1, "sel": 0},
    ],
        [
        "Test ite ret int - 1",
        32,
        ABY_SOURCE+"/build/bin/2pc_ite_ret_int",
        {"a": 32, "b": 0, "sel": 1},
        {"a": 0, "b": 45, "sel": 1},
    ],
    [
        "Test ite ret int - 2",
        45,
        ABY_SOURCE+"/build/bin/2pc_ite_ret_int",
        {"a": 32, "b": 0, "sel": 0},
        {"a": 0, "b": 45, "sel": 0},
    ],
    [
        "Test ite only if - 1",
        32,
        ABY_SOURCE+"/build/bin/2pc_ite_ret_int",
        {"a": 32, "b": 0, "sel": 1},
        {"a": 0, "b": 45, "sel": 1},
    ],
    [
        "Test ite only if - 2",
        45,
        ABY_SOURCE+"/build/bin/2pc_ite_ret_int",
        {"a": 32, "b": 0, "sel": 0},
        {"a": 0, "b": 45, "sel": 0},
    ],
]

array_tests = [
    [
        "Array sum test",
        3,
        ABY_SOURCE+"/build/bin/2pc_array_sum",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Array index test",
        3,
        ABY_SOURCE+"/build/bin/2pc_array_index",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Array index test 2",
        2,
        ABY_SOURCE+"/build/bin/2pc_array_index_2",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    # [
    #     "Array ret test",
    #     "2\n1",
    #     ABY_SOURCE+"/build/bin/2pc_array_ret",
    #     {"a": 2, "b": 0},
    #     {"a": 0, "b": 1},
    # ], 
]

c_array_tests = [
    [
        "C array test",
        2,
        ABY_SOURCE+"/build/bin/2pc_array",
        {"a": 2, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "C array test 1",
        17,
        ABY_SOURCE+"/build/bin/2pc_array_1",
        {"a": 10, "b": 0},
        {"a": 0, "b": 3},
    ], 
    [
        "C array test 2",
        17,
        ABY_SOURCE+"/build/bin/2pc_array_2",
        {"a": 10, "b": 0},
        {"a": 0, "b": 3},
    ], 
    [
        "C array test 3",
        18,
        ABY_SOURCE+"/build/bin/2pc_array_3",
        {"a": 2, "b": 0},
        {"a": 0, "b": 3},
    ], 
    [
        "C array test 3",
        30,
        ABY_SOURCE+"/build/bin/2pc_array_sum_c",
        {"a": [1,2,3,4,5], "b": 7},
        {"a": 6, "b": [1,2,3,4,5]},
    ], 
]

loop_tests = [
    [
        "Loop sum const - 1",
        10,
        ABY_SOURCE+"/build/bin/2pc_loop_sum",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Loop sum const - 2",
        10,
        ABY_SOURCE+"/build/bin/2pc_loop_sum",
        {"a": 10, "b": 0},
        {"a": 0, "b": 3},
    ],
]

function_tests = [
    [
        "Sum() two numbers - 1",
        6,
        ABY_SOURCE+"/build/bin/2pc_function_add",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Sum() two numbers - 2",
        4,
        ABY_SOURCE+"/build/bin/2pc_function_add",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
]

shift_tests = [
     [
        "Left Shift a by 1 - 1",
        20,
        ABY_SOURCE+"/build/bin/2pc_lhs",
        {"a": 10, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Left Shift a by 1 - 2",
        0,
        ABY_SOURCE+"/build/bin/2pc_lhs",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Left Shift a by 1 - 3",
        0,
        ABY_SOURCE+"/build/bin/2pc_lhs",
        {"a": 2147483648, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Right Shift a by 1 - 1",
        10,
        ABY_SOURCE+"/build/bin/2pc_rhs",
        {"a": 20, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Right Shift a by 1 - 2",
        0,
        ABY_SOURCE+"/build/bin/2pc_rhs",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
]


div_tests = [
    [
        "Divide a by 1",
        10,
        ABY_SOURCE+"/build/bin/2pc_div",
        {"a": 10, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Divide a by b - 1",
        5,
        ABY_SOURCE+"/build/bin/2pc_div",
        {"a": 10, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Divide a by b - 2",
        5,
        ABY_SOURCE+"/build/bin/2pc_div",
        {"a": 11, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Divide a by b - 3",
        0,
        ABY_SOURCE+"/build/bin/2pc_div",
        {"a": 49, "b": 0},
        {"a": 0, "b": 50},
    ], 
]

misc_tests = [
    [
        "Millionaire's problem: server has more money than client",
        0,
        ABY_SOURCE+"/build/bin/2pc_millionaire",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Millionaire's problem: server has equal money to client",
        0,
        ABY_SOURCE+"/build/bin/2pc_millionaire",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Millionaire's problem: server has less money than client",
        1,
        ABY_SOURCE+"/build/bin/2pc_millionaire",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Conversion problem",
        7,
        ABY_SOURCE+"/build/bin/2pc_conv",
        {"a": 0, "b": 0},
        {"a": 0, "b": 7},
    ], 
]

kmeans_tests = [
    [
        "kmeans",
        103,
        ABY_SOURCE+"/build/bin/2pc_kmeans",
        {"a": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], "b": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]},
        {"a": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], "b": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]},
        # {"a": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99], "b": 0},
        # {"a": 0, "b": [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99]},
    ],     
]

biomatch_tests = [
    [
        "biomatch - 1",
        14,
        ABY_SOURCE+"/build/bin/2pc_biomatch",
        {"db": [0,1,2,3,1,2,3,4,2,3,4,5,3,4,5,6,4,5,6,7,5,6,7,8,6,7,8,9,7,8,9,10,8,9,10,11,9,10,11,12,10,11,12,13,11,12,13,14,12,13,14,15,13,14,15,16,14,15,16,17,15,16,17,18,16,17,18,19,17,18,19,20,18,19,20,21,19,20,21,22,20,21,22,23,21,22,23,24,22,23,24,25,23,24,25,26,24,25,26,27,25,26,27,28,26,27,28,29,27,28,29,30,28,29,30,31,29,30,31,32,30,31,32,33,31,32,33,34,32,33,34,35,33,34,35,36,34,35,36,37,35,36,37,38,36,37,38,39,37,38,39,40,38,39,40,41,39,40,41,42,40,41,42,43,41,42,43,44,42,43,44,45,43,44,45,46,44,45,46,47,45,46,47,48,46,47,48,49,47,48,49,50,48,49,50,51,49,50,51,52,50,51,52,53,51,52,53,54,52,53,54,55,53,54,55,56,54,55,56,57,55,56,57,58,56,57,58,59,57,58,59,60,58,59,60,61,59,60,61,62,60,61,62,63,61,62,63,64,62,63,64,65,63,64,65,66,64,65,66,67,65,66,67,68,66,67,68,69,67,68,69,70,68,69,70,71,69,70,71,72,70,71,72,73,71,72,73,74,72,73,74,75,73,74,75,76,74,75,76,77,75,76,77,78,76,77,78,79,77,78,79,80,78,79,80,81,79,80,81,82,80,81,82,83,81,82,83,84,82,83,84,85,83,84,85,86,84,85,86,87,85,86,87,88,86,87,88,89,87,88,89,90,88,89,90,91,89,90,91,92,90,91,92,93,91,92,93,94,92,93,94,95,93,94,95,96,94,95,96,97,95,96,97,98,96,97,98,99,97,98,99,100,98,99,100,101,99,100,101,102,100,101,102,103,101,102,103,104,102,103,104,105,103,104,105,106,104,105,106,107,105,106,107,108,106,107,108,109,107,108,109,110,108,109,110,111,109,110,111,112,110,111,112,113,111,112,113,114,112,113,114,115,113,114,115,116,114,115,116,117,115,116,117,118,116,117,118,119,117,118,119,120,118,119,120,121,119,120,121,122,120,121,122,123,121,122,123,124,122,123,124,125,123,124,125,126,124,125,126,127,125,126,127,128,126,127,128,129,127,128,129,130,128,129,130,131,129,130,131,132,130,131,132,133,131,132,133,134,132,133,134,135,133,134,135,136,134,135,136,137,135,136,137,138,136,137,138,139,137,138,139,140,138,139,140,141,139,140,141,142,140,141,142,143,141,142,143,144,142,143,144,145,143,144,145,146,144,145,146,147,145,146,147,148,146,147,148,149,147,148,149,150,148,149,150,151,149,150,151,152,150,151,152,153,151,152,153,154,152,153,154,155,153,154,155,156,154,155,156,157,155,156,157,158,156,157,158,159,157,158,159,160,158,159,160,161,159,160,161,162,160,161,162,163,161,162,163,164,162,163,164,165,163,164,165,166,164,165,166,167,165,166,167,168,166,167,168,169,167,168,169,170,168,169,170,171,169,170,171,172,170,171,172,173,171,172,173,174,172,173,174,175,173,174,175,176,174,175,176,177,175,176,177,178,176,177,178,179,177,178,179,180,178,179,180,181,179,180,181,182,180,181,182,183,181,182,183,184,182,183,184,185,183,184,185,186,184,185,186,187,185,186,187,188,186,187,188,189,187,188,189,190,188,189,190,191,189,190,191,192,190,191,192,193,191,192,193,194,192,193,194,195,193,194,195,196,194,195,196,197,195,196,197,198,196,197,198,199,197,198,199,200,198,199,200,201,199,200,201,202,200,201,202,203,201,202,203,204,202,203,204,205,203,204,205,206,204,205,206,207,205,206,207,208,206,207,208,209,207,208,209,210,208,209,210,211,209,210,211,212,210,211,212,213,211,212,213,214,212,213,214,215,213,214,215,216,214,215,216,217,215,216,217,218,216,217,218,219,217,218,219,220,218,219,220,221,219,220,221,222,220,221,222,223,221,222,223,224,222,223,224,225,223,224,225,226,224,225,226,227,225,226,227,228,226,227,228,229,227,228,229,230,228,229,230,231,229,230,231,232,230,231,232,233,231,232,233,234,232,233,234,235,233,234,235,236,234,235,236,237,235,236,237,238,236,237,238,239,237,238,239,240,238,239,240,241,239,240,241,242,240,241,242,243,241,242,243,244,242,243,244,245,243,244,245,246,244,245,246,247,245,246,247,248,246,247,248,249,247,248,249,250,248,249,250,251,249,250,251,252,250,251,252,253,251,252,253,254,252,253,254,255,253,254,255,256,254,255,256,257,255,256,257,258], "sample": [0,0,0,0]},
        {"db": [0,1,2,3,1,2,3,4,2,3,4,5,3,4,5,6,4,5,6,7,5,6,7,8,6,7,8,9,7,8,9,10,8,9,10,11,9,10,11,12,10,11,12,13,11,12,13,14,12,13,14,15,13,14,15,16,14,15,16,17,15,16,17,18,16,17,18,19,17,18,19,20,18,19,20,21,19,20,21,22,20,21,22,23,21,22,23,24,22,23,24,25,23,24,25,26,24,25,26,27,25,26,27,28,26,27,28,29,27,28,29,30,28,29,30,31,29,30,31,32,30,31,32,33,31,32,33,34,32,33,34,35,33,34,35,36,34,35,36,37,35,36,37,38,36,37,38,39,37,38,39,40,38,39,40,41,39,40,41,42,40,41,42,43,41,42,43,44,42,43,44,45,43,44,45,46,44,45,46,47,45,46,47,48,46,47,48,49,47,48,49,50,48,49,50,51,49,50,51,52,50,51,52,53,51,52,53,54,52,53,54,55,53,54,55,56,54,55,56,57,55,56,57,58,56,57,58,59,57,58,59,60,58,59,60,61,59,60,61,62,60,61,62,63,61,62,63,64,62,63,64,65,63,64,65,66,64,65,66,67,65,66,67,68,66,67,68,69,67,68,69,70,68,69,70,71,69,70,71,72,70,71,72,73,71,72,73,74,72,73,74,75,73,74,75,76,74,75,76,77,75,76,77,78,76,77,78,79,77,78,79,80,78,79,80,81,79,80,81,82,80,81,82,83,81,82,83,84,82,83,84,85,83,84,85,86,84,85,86,87,85,86,87,88,86,87,88,89,87,88,89,90,88,89,90,91,89,90,91,92,90,91,92,93,91,92,93,94,92,93,94,95,93,94,95,96,94,95,96,97,95,96,97,98,96,97,98,99,97,98,99,100,98,99,100,101,99,100,101,102,100,101,102,103,101,102,103,104,102,103,104,105,103,104,105,106,104,105,106,107,105,106,107,108,106,107,108,109,107,108,109,110,108,109,110,111,109,110,111,112,110,111,112,113,111,112,113,114,112,113,114,115,113,114,115,116,114,115,116,117,115,116,117,118,116,117,118,119,117,118,119,120,118,119,120,121,119,120,121,122,120,121,122,123,121,122,123,124,122,123,124,125,123,124,125,126,124,125,126,127,125,126,127,128,126,127,128,129,127,128,129,130,128,129,130,131,129,130,131,132,130,131,132,133,131,132,133,134,132,133,134,135,133,134,135,136,134,135,136,137,135,136,137,138,136,137,138,139,137,138,139,140,138,139,140,141,139,140,141,142,140,141,142,143,141,142,143,144,142,143,144,145,143,144,145,146,144,145,146,147,145,146,147,148,146,147,148,149,147,148,149,150,148,149,150,151,149,150,151,152,150,151,152,153,151,152,153,154,152,153,154,155,153,154,155,156,154,155,156,157,155,156,157,158,156,157,158,159,157,158,159,160,158,159,160,161,159,160,161,162,160,161,162,163,161,162,163,164,162,163,164,165,163,164,165,166,164,165,166,167,165,166,167,168,166,167,168,169,167,168,169,170,168,169,170,171,169,170,171,172,170,171,172,173,171,172,173,174,172,173,174,175,173,174,175,176,174,175,176,177,175,176,177,178,176,177,178,179,177,178,179,180,178,179,180,181,179,180,181,182,180,181,182,183,181,182,183,184,182,183,184,185,183,184,185,186,184,185,186,187,185,186,187,188,186,187,188,189,187,188,189,190,188,189,190,191,189,190,191,192,190,191,192,193,191,192,193,194,192,193,194,195,193,194,195,196,194,195,196,197,195,196,197,198,196,197,198,199,197,198,199,200,198,199,200,201,199,200,201,202,200,201,202,203,201,202,203,204,202,203,204,205,203,204,205,206,204,205,206,207,205,206,207,208,206,207,208,209,207,208,209,210,208,209,210,211,209,210,211,212,210,211,212,213,211,212,213,214,212,213,214,215,213,214,215,216,214,215,216,217,215,216,217,218,216,217,218,219,217,218,219,220,218,219,220,221,219,220,221,222,220,221,222,223,221,222,223,224,222,223,224,225,223,224,225,226,224,225,226,227,225,226,227,228,226,227,228,229,227,228,229,230,228,229,230,231,229,230,231,232,230,231,232,233,231,232,233,234,232,233,234,235,233,234,235,236,234,235,236,237,235,236,237,238,236,237,238,239,237,238,239,240,238,239,240,241,239,240,241,242,240,241,242,243,241,242,243,244,242,243,244,245,243,244,245,246,244,245,246,247,245,246,247,248,246,247,248,249,247,248,249,250,248,249,250,251,249,250,251,252,250,251,252,253,251,252,253,254,252,253,254,255,253,254,255,256,254,255,256,257,255,256,257,258], "sample": [0,0,0,0]}
    ],   
    [
        "biomatch - 2",
        0,
        ABY_SOURCE+"/build/bin/2pc_biomatch",
        {"db": [0,1,2,3,1,2,3,4,2,3,4,5,3,4,5,6,4,5,6,7,5,6,7,8,6,7,8,9,7,8,9,10,8,9,10,11,9,10,11,12,10,11,12,13,11,12,13,14,12,13,14,15,13,14,15,16,14,15,16,17,15,16,17,18,16,17,18,19,17,18,19,20,18,19,20,21,19,20,21,22,20,21,22,23,21,22,23,24,22,23,24,25,23,24,25,26,24,25,26,27,25,26,27,28,26,27,28,29,27,28,29,30,28,29,30,31,29,30,31,32,30,31,32,33,31,32,33,34,32,33,34,35,33,34,35,36,34,35,36,37,35,36,37,38,36,37,38,39,37,38,39,40,38,39,40,41,39,40,41,42,40,41,42,43,41,42,43,44,42,43,44,45,43,44,45,46,44,45,46,47,45,46,47,48,46,47,48,49,47,48,49,50,48,49,50,51,49,50,51,52,50,51,52,53,51,52,53,54,52,53,54,55,53,54,55,56,54,55,56,57,55,56,57,58,56,57,58,59,57,58,59,60,58,59,60,61,59,60,61,62,60,61,62,63,61,62,63,64,62,63,64,65,63,64,65,66,64,65,66,67,65,66,67,68,66,67,68,69,67,68,69,70,68,69,70,71,69,70,71,72,70,71,72,73,71,72,73,74,72,73,74,75,73,74,75,76,74,75,76,77,75,76,77,78,76,77,78,79,77,78,79,80,78,79,80,81,79,80,81,82,80,81,82,83,81,82,83,84,82,83,84,85,83,84,85,86,84,85,86,87,85,86,87,88,86,87,88,89,87,88,89,90,88,89,90,91,89,90,91,92,90,91,92,93,91,92,93,94,92,93,94,95,93,94,95,96,94,95,96,97,95,96,97,98,96,97,98,99,97,98,99,100,98,99,100,101,99,100,101,102,100,101,102,103,101,102,103,104,102,103,104,105,103,104,105,106,104,105,106,107,105,106,107,108,106,107,108,109,107,108,109,110,108,109,110,111,109,110,111,112,110,111,112,113,111,112,113,114,112,113,114,115,113,114,115,116,114,115,116,117,115,116,117,118,116,117,118,119,117,118,119,120,118,119,120,121,119,120,121,122,120,121,122,123,121,122,123,124,122,123,124,125,123,124,125,126,124,125,126,127,125,126,127,128,126,127,128,129,127,128,129,130,128,129,130,131,129,130,131,132,130,131,132,133,131,132,133,134,132,133,134,135,133,134,135,136,134,135,136,137,135,136,137,138,136,137,138,139,137,138,139,140,138,139,140,141,139,140,141,142,140,141,142,143,141,142,143,144,142,143,144,145,143,144,145,146,144,145,146,147,145,146,147,148,146,147,148,149,147,148,149,150,148,149,150,151,149,150,151,152,150,151,152,153,151,152,153,154,152,153,154,155,153,154,155,156,154,155,156,157,155,156,157,158,156,157,158,159,157,158,159,160,158,159,160,161,159,160,161,162,160,161,162,163,161,162,163,164,162,163,164,165,163,164,165,166,164,165,166,167,165,166,167,168,166,167,168,169,167,168,169,170,168,169,170,171,169,170,171,172,170,171,172,173,171,172,173,174,172,173,174,175,173,174,175,176,174,175,176,177,175,176,177,178,176,177,178,179,177,178,179,180,178,179,180,181,179,180,181,182,180,181,182,183,181,182,183,184,182,183,184,185,183,184,185,186,184,185,186,187,185,186,187,188,186,187,188,189,187,188,189,190,188,189,190,191,189,190,191,192,190,191,192,193,191,192,193,194,192,193,194,195,193,194,195,196,194,195,196,197,195,196,197,198,196,197,198,199,197,198,199,200,198,199,200,201,199,200,201,202,200,201,202,203,201,202,203,204,202,203,204,205,203,204,205,206,204,205,206,207,205,206,207,208,206,207,208,209,207,208,209,210,208,209,210,211,209,210,211,212,210,211,212,213,211,212,213,214,212,213,214,215,213,214,215,216,214,215,216,217,215,216,217,218,216,217,218,219,217,218,219,220,218,219,220,221,219,220,221,222,220,221,222,223,221,222,223,224,222,223,224,225,223,224,225,226,224,225,226,227,225,226,227,228,226,227,228,229,227,228,229,230,228,229,230,231,229,230,231,232,230,231,232,233,231,232,233,234,232,233,234,235,233,234,235,236,234,235,236,237,235,236,237,238,236,237,238,239,237,238,239,240,238,239,240,241,239,240,241,242,240,241,242,243,241,242,243,244,242,243,244,245,243,244,245,246,244,245,246,247,245,246,247,248,246,247,248,249,247,248,249,250,248,249,250,251,249,250,251,252,250,251,252,253,251,252,253,254,252,253,254,255,253,254,255,256,254,255,256,257,255,256,257,258], "sample": [0,0,0,0]},
        {"db": [0,1,2,3,1,2,3,4,2,3,4,5,3,4,5,6,4,5,6,7,5,6,7,8,6,7,8,9,7,8,9,10,8,9,10,11,9,10,11,12,10,11,12,13,11,12,13,14,12,13,14,15,13,14,15,16,14,15,16,17,15,16,17,18,16,17,18,19,17,18,19,20,18,19,20,21,19,20,21,22,20,21,22,23,21,22,23,24,22,23,24,25,23,24,25,26,24,25,26,27,25,26,27,28,26,27,28,29,27,28,29,30,28,29,30,31,29,30,31,32,30,31,32,33,31,32,33,34,32,33,34,35,33,34,35,36,34,35,36,37,35,36,37,38,36,37,38,39,37,38,39,40,38,39,40,41,39,40,41,42,40,41,42,43,41,42,43,44,42,43,44,45,43,44,45,46,44,45,46,47,45,46,47,48,46,47,48,49,47,48,49,50,48,49,50,51,49,50,51,52,50,51,52,53,51,52,53,54,52,53,54,55,53,54,55,56,54,55,56,57,55,56,57,58,56,57,58,59,57,58,59,60,58,59,60,61,59,60,61,62,60,61,62,63,61,62,63,64,62,63,64,65,63,64,65,66,64,65,66,67,65,66,67,68,66,67,68,69,67,68,69,70,68,69,70,71,69,70,71,72,70,71,72,73,71,72,73,74,72,73,74,75,73,74,75,76,74,75,76,77,75,76,77,78,76,77,78,79,77,78,79,80,78,79,80,81,79,80,81,82,80,81,82,83,81,82,83,84,82,83,84,85,83,84,85,86,84,85,86,87,85,86,87,88,86,87,88,89,87,88,89,90,88,89,90,91,89,90,91,92,90,91,92,93,91,92,93,94,92,93,94,95,93,94,95,96,94,95,96,97,95,96,97,98,96,97,98,99,97,98,99,100,98,99,100,101,99,100,101,102,100,101,102,103,101,102,103,104,102,103,104,105,103,104,105,106,104,105,106,107,105,106,107,108,106,107,108,109,107,108,109,110,108,109,110,111,109,110,111,112,110,111,112,113,111,112,113,114,112,113,114,115,113,114,115,116,114,115,116,117,115,116,117,118,116,117,118,119,117,118,119,120,118,119,120,121,119,120,121,122,120,121,122,123,121,122,123,124,122,123,124,125,123,124,125,126,124,125,126,127,125,126,127,128,126,127,128,129,127,128,129,130,128,129,130,131,129,130,131,132,130,131,132,133,131,132,133,134,132,133,134,135,133,134,135,136,134,135,136,137,135,136,137,138,136,137,138,139,137,138,139,140,138,139,140,141,139,140,141,142,140,141,142,143,141,142,143,144,142,143,144,145,143,144,145,146,144,145,146,147,145,146,147,148,146,147,148,149,147,148,149,150,148,149,150,151,149,150,151,152,150,151,152,153,151,152,153,154,152,153,154,155,153,154,155,156,154,155,156,157,155,156,157,158,156,157,158,159,157,158,159,160,158,159,160,161,159,160,161,162,160,161,162,163,161,162,163,164,162,163,164,165,163,164,165,166,164,165,166,167,165,166,167,168,166,167,168,169,167,168,169,170,168,169,170,171,169,170,171,172,170,171,172,173,171,172,173,174,172,173,174,175,173,174,175,176,174,175,176,177,175,176,177,178,176,177,178,179,177,178,179,180,178,179,180,181,179,180,181,182,180,181,182,183,181,182,183,184,182,183,184,185,183,184,185,186,184,185,186,187,185,186,187,188,186,187,188,189,187,188,189,190,188,189,190,191,189,190,191,192,190,191,192,193,191,192,193,194,192,193,194,195,193,194,195,196,194,195,196,197,195,196,197,198,196,197,198,199,197,198,199,200,198,199,200,201,199,200,201,202,200,201,202,203,201,202,203,204,202,203,204,205,203,204,205,206,204,205,206,207,205,206,207,208,206,207,208,209,207,208,209,210,208,209,210,211,209,210,211,212,210,211,212,213,211,212,213,214,212,213,214,215,213,214,215,216,214,215,216,217,215,216,217,218,216,217,218,219,217,218,219,220,218,219,220,221,219,220,221,222,220,221,222,223,221,222,223,224,222,223,224,225,223,224,225,226,224,225,226,227,225,226,227,228,226,227,228,229,227,228,229,230,228,229,230,231,229,230,231,232,230,231,232,233,231,232,233,234,232,233,234,235,233,234,235,236,234,235,236,237,235,236,237,238,236,237,238,239,237,238,239,240,238,239,240,241,239,240,241,242,240,241,242,243,241,242,243,244,242,243,244,245,243,244,245,246,244,245,246,247,245,246,247,248,246,247,248,249,247,248,249,250,248,249,250,251,249,250,251,252,250,251,252,253,251,252,253,254,252,253,254,255,253,254,255,256,254,255,256,257,255,256,257,258], "sample": [1,2,3,4]}
    ],   
]

ilp_benchmark_tests = [
    [
        "ilp bench - array sum 1",
        1000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_1",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],     
    [
        "ilp bench - array sum 2",
        2000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_2",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],   
    [
        "ilp bench - array sum 3",
        3000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_3",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],   
    [
        "ilp bench - array sum 4",
        4000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_4",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],   
    [
        "ilp bench - array sum 5",
        5000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_5",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],   
    [
        "ilp bench - array sum 6",
        6000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_6",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],  
    [
        "ilp bench - array sum 7",
        7000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_7",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],  
        [
        "ilp bench - array sum 8",
        8000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_8",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],  
        [
        "ilp bench - array sum 9",
        9000,
        ABY_SOURCE+"/build/bin/2pc_ilp_bench_9",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ],  

]

millionaires_test = [
    [
        "Millionaire's problem",
        0,
        ABY_SOURCE+"/build/bin/2pc_millionaires",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
]

# ree_tests = [
#     [
#         "Array sum test 2",
#         6,
#         ABY_SOURCE+"/build/bin/2pc_array_sum_2",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ], 
# ]
