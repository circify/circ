boolean_tests = [
    [
        "Boolean && - 1",
        "2pc_boolean_and",
        "./scripts/seal_tests/test_inputs/and_1.txt",
    ],
    [
        "Boolean && - 2",
        "2pc_boolean_and",
        "./scripts/seal_tests/test_inputs/and_2.txt",
    ],
    [
        "Boolean && - 3",
        "2pc_boolean_and",
        "./scripts/seal_tests/test_inputs/and_3.txt",
    ],
    [
        "Boolean && - 4",
        "2pc_boolean_and",
        "./scripts/seal_tests/test_inputs/and_4.txt",
    ],
    [
        "Boolean || - 1",
        "2pc_boolean_or",
        "./scripts/seal_tests/test_inputs/or_1.txt",
    ],
    [
        "Boolean || - 2",
        "2pc_boolean_or",
        "./scripts/seal_tests/test_inputs/or_2.txt",

    ],
    [
        "Boolean || - 3",
        "2pc_boolean_or",
        "./scripts/seal_tests/test_inputs/or_3.txt",

    ],
    [
        "Boolean || - 4",
        "2pc_boolean_or",
        "./scripts/seal_tests/test_inputs/or_4.txt",
    ],
    [
        "Boolean == - 1",
        "2pc_boolean_equals",
        "./scripts/seal_tests/test_inputs/eq_1.txt",
    ],
    [
        "Boolean == - 2",
        "2pc_boolean_equals",
        "./scripts/seal_tests/test_inputs/eq_2.txt",
    ],
]

arithmetic_tests = [
    [
        "Add two numbers",
        "2pc_add",
        "./scripts/seal_tests/test_inputs/add.txt",
    ], 
    [
        "Multiply two numbers - 1",
        "2pc_mult",
        "./scripts/seal_tests/test_inputs/mult_1.txt",
    ], 
    [
        "Multiply two numbers - 2",
        "2pc_mult",
        "./scripts/seal_tests/test_inputs/mult_2.txt",
    ], 
    [
        "Multiply two numbers - 3",
        "2pc_mult",
        "./scripts/seal_tests/test_inputs/mult_3.txt",
    ], 
    [
        "Multiply two numbers together and add with public value",
        "2pc_mult_add_pub",
        "./scripts/seal_tests/test_inputs/mult_add_pub_1.txt",
    ], 
    [
        "Multiply two numbers together and add with public value, check only server side public value is added",
        "2pc_mult_add_pub",
        "./scripts/seal_tests/test_inputs/mult_add_pub_2.txt",
    ], 
]
nary_arithmetic_tests = [
    [
        "Test a + b + c",
        "2pc_nary_arithmetic_add",
        "./scripts/seal_tests/test_inputs/nary_add.txt",
    ],
]

nary_boolean_tests = [
    [
        "Test a & b & c",
        "2pc_nary_boolean_and",
        "./scripts/seal_tests/test_inputs/nary_and.txt",
    ],
]