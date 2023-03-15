new_tests = [
    [
        "new",
        "playground",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
]

arithmetic_tests = [
    [
        "Add two numbers",
        "2pc_add",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
    [
        "Subtract two numbers",
        "2pc_sub",
        "./scripts/aby_tests/test_inputs/sub_1.txt",
    ],
    [
        "Subtract two numbers, negative -1 == 4294967295 because u32",
        "2pc_sub",
        "./scripts/aby_tests/test_inputs/sub_2.txt",
    ],
    [
        "Multiply two numbers - 1",
        "2pc_mult",
        "./scripts/aby_tests/test_inputs/mult_1.txt",
    ],
    [
        "Multiply two numbers - 2",
        "2pc_mult",
        "./scripts/aby_tests/test_inputs/mult_2.txt",
    ],
    [
        "Multiply two numbers - 3",
        "2pc_mult",
        "./scripts/aby_tests/test_inputs/mult_3.txt",
    ],
    [
        # only server side public value works
        "Multiply two numbers together and add with public value",
        "2pc_mult_add_pub",
        "./scripts/aby_tests/test_inputs/mult_add_pub_1.txt",
    ],
    [
        # only server side public value works
        "Multiply two numbers together and add with public value, check only server side public value is added",
        "2pc_mult_add_pub",
        "./scripts/aby_tests/test_inputs/mult_add_pub_2.txt",
    ],
]

arithmetic_boolean_tests = [
    [
        "Test two numbers are equal - 1",
        "2pc_int_equals",
        "./scripts/aby_tests/test_inputs/eq_1.txt",
    ],
    [
        "Test two numbers are equal - 2",
        "2pc_int_equals",
        "./scripts/aby_tests/test_inputs/eq_2.txt",
    ],
    [
        "Test int > int - 1",
        "2pc_int_greater_than",
        "./scripts/aby_tests/test_inputs/gt_1.txt",
    ],
    [
        "Test int > int - 2",
        "2pc_int_greater_than",
        "./scripts/aby_tests/test_inputs/gt_2.txt",
    ],
    [
        "Test int > int - 3",
        "2pc_int_greater_than",
        "./scripts/aby_tests/test_inputs/gt_3.txt",
    ],
    [
        "Test int >= int - 1",
        "2pc_int_greater_equals",
        "./scripts/aby_tests/test_inputs/ge_1.txt",
    ],
    [
        "Test int >= int - 2",
        "2pc_int_greater_equals",
        "./scripts/aby_tests/test_inputs/ge_2.txt",
    ],
    [
        "Test int >= int - 3",
        "2pc_int_greater_equals",
        "./scripts/aby_tests/test_inputs/ge_3.txt",
    ],
    [
        "Test int < int - 1",
        "2pc_int_less_than",
        "./scripts/aby_tests/test_inputs/lt_1.txt",
    ],
    [
        "Test int < int - 2",
        "2pc_int_less_than",
        "./scripts/aby_tests/test_inputs/lt_2.txt",
    ],
    [
        "Test int < int - 3",
        "2pc_int_less_than",
        "./scripts/aby_tests/test_inputs/lt_3.txt",
    ],
    [
        "Test int <= int - 1",
        "2pc_int_less_equals",
        "./scripts/aby_tests/test_inputs/le_1.txt",
    ],
    [
        "Test int <= int - 2",
        "2pc_int_less_equals",
        "./scripts/aby_tests/test_inputs/le_2.txt",
    ],
    [
        "Test int <= int - 3",
        "2pc_int_less_equals",
        "./scripts/aby_tests/test_inputs/le_3.txt",
    ],
]

unsigned_arithmetic_tests = [
    [
        "Add two unsigned numbers",
        "2pc_add_unsigned",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
]

nary_arithmetic_tests = [
    [
        "Test a + b + c",
        "2pc_nary_arithmetic_add",
        "./scripts/aby_tests/test_inputs/nary_add.txt",
    ],
]

bitwise_tests = [
    [
        "Bitwise & - 1",
        "2pc_bitwise_and",
        "./scripts/aby_tests/test_inputs/and_1.txt",
    ],
    [
        "Bitwise & - 2",
        "2pc_bitwise_and",
        "./scripts/aby_tests/test_inputs/and_2.txt",
    ],
    [
        "Bitwise & - 3",
        "2pc_bitwise_and",
        "./scripts/aby_tests/test_inputs/and_3.txt",
    ],
    [
        "Bitwise & - 4",
        "2pc_bitwise_and",
        "./scripts/aby_tests/test_inputs/and_4.txt",
    ],
    [
        "Bitwise | - 1",
        "2pc_bitwise_or",
        "./scripts/aby_tests/test_inputs/or_1.txt",
    ],
    [
        "Bitwise | - 2",
        "2pc_bitwise_or",
        "./scripts/aby_tests/test_inputs/or_2.txt",
    ],
    [
        "Bitwise | - 3",
        "2pc_bitwise_or",
        "./scripts/aby_tests/test_inputs/or_3.txt",
    ],
    [
        "Bitwise | - 4",
        "2pc_bitwise_or",
        "./scripts/aby_tests/test_inputs/or_4.txt",
    ],
    [
        "Bitwise ^ - 1",
        "2pc_bitwise_xor",
        "./scripts/aby_tests/test_inputs/xor_1.txt",

    ],
    [
        "Bitwise ^ - 2",
        "2pc_bitwise_xor",
        "./scripts/aby_tests/test_inputs/xor_2.txt",
    ],
    [
        "Bitwise ^ - 3",
        "2pc_bitwise_xor",
        "./scripts/aby_tests/test_inputs/xor_3.txt",
    ],
    [
        "Bitwise ^ - 4",
        "2pc_bitwise_xor",
        "./scripts/aby_tests/test_inputs/xor_4.txt",
    ],
]

boolean_tests = [
    [
        "Boolean && - 1",
        "2pc_boolean_and",
        "./scripts/aby_tests/test_inputs/and_1.txt",
    ],
    [
        "Boolean && - 2",
        "2pc_boolean_and",
        "./scripts/aby_tests/test_inputs/and_2.txt",
    ],
    [
        "Boolean && - 3",
        "2pc_boolean_and",
        "./scripts/aby_tests/test_inputs/and_3.txt",
    ],
    [
        "Boolean && - 4",
        "2pc_boolean_and",
        "./scripts/aby_tests/test_inputs/and_4.txt",
    ],
    [
        "Boolean || - 1",
        "2pc_boolean_or",
        "./scripts/aby_tests/test_inputs/or_1.txt",
    ],
    [
        "Boolean || - 2",
        "2pc_boolean_or",
        "./scripts/aby_tests/test_inputs/or_2.txt",

    ],
    [
        "Boolean || - 3",
        "2pc_boolean_or",
        "./scripts/aby_tests/test_inputs/or_3.txt",

    ],
    [
        "Boolean || - 4",
        "2pc_boolean_or",
        "./scripts/aby_tests/test_inputs/or_4.txt",
    ],
    [
        "Boolean == - 1",
        "2pc_boolean_equals",
        "./scripts/aby_tests/test_inputs/eq_1.txt",
    ],
    [
        "Boolean == - 2",
        "2pc_boolean_equals",
        "./scripts/aby_tests/test_inputs/eq_2.txt",
    ],
]

nary_boolean_tests = [
    [
        "Test a & b & c",
        "2pc_nary_boolean_and",
        "./scripts/aby_tests/test_inputs/nary_and.txt",
    ],
]


const_arith_tests = [
    [
        "Test add client int + server int to const value",
        "2pc_const_arith",
        "./scripts/aby_tests/test_inputs/const_add.txt",
    ],
]

const_bool_tests = [
    [
        "Test server value == const value - 1",
        "2pc_const_bool",
        "./scripts/aby_tests/test_inputs/const_eq_1.txt",
    ],
    [
        "Test server value == const value - 2",
        "2pc_const_bool",
        "./scripts/aby_tests/test_inputs/const_eq_2.txt",
    ],
]

ite_tests = [
    [
        "Test ite ret bool - 1",
        "2pc_ite_ret_bool",
        "./scripts/aby_tests/test_inputs/ite_1.txt",
    ],
    [
        "Test ite ret bool - 2",
        "2pc_ite_ret_bool",
        "./scripts/aby_tests/test_inputs/ite_2.txt",
    ],
    [
        "Test ite ret int - 1",
        "2pc_ite_ret_int",
        "./scripts/aby_tests/test_inputs/ite_1.txt",
    ],
    [
        "Test ite ret int - 2",
        "2pc_ite_ret_int",
        "./scripts/aby_tests/test_inputs/ite_2.txt",
    ],
    [
        "Test ite only if - 1",
        "2pc_ite_only_if",
        "./scripts/aby_tests/test_inputs/ite_1.txt",
    ],
    [
        "Test ite only if - 2",
        "2pc_ite_only_if",
        "./scripts/aby_tests/test_inputs/ite_2.txt",
    ],
]

array_tests = [
    [
        "Array sum test",
        "2pc_array_sum",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
    [
        "Array index test",
        "2pc_array_index",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
]

c_array_tests = [
    [
        "C array test",
        "2pc_array",
        "./scripts/aby_tests/test_inputs/array.txt",
    ],
    [
        "C array test 1",
        "2pc_array_1",
        "./scripts/aby_tests/test_inputs/array_1.txt",
    ],
    [
        "C array test 2",
        "2pc_array_2",
        "./scripts/aby_tests/test_inputs/array_2.txt",
    ],
    [
        "C array test 3",
        "2pc_array_3",
        "./scripts/aby_tests/test_inputs/array_3.txt",
    ],
    [
        "C array test 4",
        "2pc_array_sum_c",
        "./scripts/aby_tests/test_inputs/array_4.txt",
    ],
]

loop_tests = [
    [
        "Loop sum const - 1",
        "2pc_loop_sum",
        "./scripts/aby_tests/test_inputs/loop_1.txt",
    ],
    [
        "Loop sum const - 2",
        "2pc_loop_sum",
        "./scripts/aby_tests/test_inputs/loop_2.txt",
    ],
]

function_tests = [
    [
        "Sum() two numbers - 1",
        "2pc_function_add",
        "./scripts/aby_tests/test_inputs/add_2.txt",
    ],
    [
        "Subtract two numbers",
        "function_arg_order",
        "./scripts/aby_tests/test_inputs/sub_1.txt",
    ],
]

struct_tests = [
    [
        "Struct add",
        "2pc_struct_add",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
    # [
    #     "Struct array add",
    #     "2pc_struct_array_add",
    #     "./scripts/aby_tests/test_inputs/add.txt",
    # ],
]

matrix_tests = [
    [
        "Matrix add",
        "2pc_matrix_add",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
    [
        "Matrix assign add",
        "2pc_matrix_assign_add",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
    [
        "Matrix ptr add",
        "2pc_matrix_ptr_add",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
]

ptr_tests = [
    [
        "Ptr add",
        "2pc_ptr_add",
        "./scripts/aby_tests/test_inputs/add.txt",
    ],
]

shift_tests = [
    [
        "Left Shift a by 1 - 1",
        "2pc_lhs",
        "./scripts/aby_tests/test_inputs/lsh_1.txt",
    ],
    [
        "Left Shift a by 1 - 2",
        "2pc_lhs",
        "./scripts/aby_tests/test_inputs/lsh_2.txt",
    ],
    [
        "Right Shift a by 1 - 1",
        "2pc_rhs",
        "./scripts/aby_tests/test_inputs/rsh_1.txt",
    ],
    [
        "Right Shift a by 1 - 2",
        "2pc_rhs",
        "./scripts/aby_tests/test_inputs/rsh_2.txt",
    ],
]


div_tests = [
    [
        "Divide a by 1",
        "2pc_div",
        "./scripts/aby_tests/test_inputs/div_1.txt",
    ],
    [
        "Divide a by b - 1",
        "2pc_div",
        "./scripts/aby_tests/test_inputs/div_2.txt",
    ],
    [
        "Divide a by b - 2",
        "2pc_div",
        "./scripts/aby_tests/test_inputs/div_3.txt",
    ],
    [
        "Divide a by b - 3",
        "2pc_div",
        "./scripts/aby_tests/test_inputs/div_4.txt",
    ],
]

mod_tests = [
    [
        "Mod two numbers - 1",
        "2pc_mod",
        "./scripts/aby_tests/test_inputs/mod_1.txt",
    ],
    [
        "Mod two numbers - 2",
        "2pc_mod",
        "./scripts/aby_tests/test_inputs/mod_2.txt",
    ],
    [
        "Mod two numbers - 3",
        "2pc_mod",
        "./scripts/aby_tests/test_inputs/mod_3.txt",
    ],
]

c_misc_tests = [
    [
        "Millionaire's problem: server has more money than client",
        "2pc_millionaires",
        "./scripts/aby_tests/test_inputs/lt_1.txt",
    ],
    [
        "Millionaire's problem: server has equal money to client",
        "2pc_millionaires",
        "./scripts/aby_tests/test_inputs/lt_2.txt",
    ],
    [
        "Millionaire's problem: server has less money than client",
        "2pc_millionaires",
        "./scripts/aby_tests/test_inputs/lt_3.txt",
    ],
    [
        "Multivariables",
        "2pc_multi_var",
        "./scripts/aby_tests/test_inputs/multi.txt",
    ]
]

zok_misc_tests = [
    [
        "Millionaire's problem: server has more money than client",
        "2pc_millionaires",
        "./scripts/aby_tests/test_inputs/lt_1.txt",
    ],
    [
        "Millionaire's problem: server has equal money to client",
        "2pc_millionaires",
        "./scripts/aby_tests/test_inputs/lt_2.txt",
    ],
    [
        "Millionaire's problem: server has less money than client",
        "2pc_millionaires",
        "./scripts/aby_tests/test_inputs/lt_3.txt",
    ],
]

biomatch_tests = [
    [
        "biomatch - 1",
        "2pc_biomatch",
        "./scripts/aby_tests/test_inputs/biomatch_1.txt",
    ],
    [
        "biomatch - 2",
        "2pc_biomatch",
        "./scripts/aby_tests/test_inputs/biomatch_2.txt",
    ],
]

kmeans_tests = [
    [
        "kmeans",
        "2pc_kmeans",
        "./scripts/aby_tests/test_inputs/kmeans.txt",
    ],
]

kmeans_tests_2 = [
    [
        "kmeans",
        "2pc_kmeans_og",
        "./scripts/aby_tests/test_inputs/kmeans.txt",
    ],
]

gauss_tests = [
    [
        "gauss",
        "2pc_gauss",
        "./scripts/aby_tests/test_inputs/gauss.txt",
    ],
]

db_tests = [
    [
        "db join",
        "db_join",
        "./scripts/aby_tests/test_inputs/db_join.txt",
    ],
]

benchmark_tests = [
    [
        "biomatch - 1",
        "2pc_biomatch",
        "./scripts/aby_tests/test_inputs/biomatch_benchmark_1.txt",
    ],
]

# ilp_benchmark_tests = [
#     [
#         "ilp bench - array sum 1",
#         1000,
#         "2pc_ilp_bench_1",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
#     [
#         "ilp bench - array sum 2",
#         2000,
#         "2pc_ilp_bench_2",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
#     [
#         "ilp bench - array sum 3",
#         3000,
#         "2pc_ilp_bench_3",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
#     [
#         "ilp bench - array sum 4",
#         4000,
#         "2pc_ilp_bench_4",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
#     [
#         "ilp bench - array sum 5",
#         5000,
#         "2pc_ilp_bench_5",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
#     [
#         "ilp bench - array sum 6",
#         6000,
#         "2pc_ilp_bench_6",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
#     [
#         "ilp bench - array sum 7",
#         7000,
#         "2pc_ilp_bench_7",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
#         [
#         "ilp bench - array sum 8",
#         8000,
#         "2pc_ilp_bench_8",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
#         [
#         "ilp bench - array sum 9",
#         9000,
#         "2pc_ilp_bench_9",
#         {"a": 2, "b": 0},
#         {"a": 0, "b": 1},
#     ],
# ]
