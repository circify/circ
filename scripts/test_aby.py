from subprocess import Popen, PIPE
from typing import List
import time 

arithmetic_tests = [
    [
        "Add two numbers - 1",
        3,
        "./third_party/ABY/build/bin/2pc_add_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Add two numbers - 2",
        2,
        "./third_party/ABY/build/bin/2pc_add_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Subtract two numbers",
        1,
        "./third_party/ABY/build/bin/2pc_sub_test",
        {"a": 3, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Subtract two numbers, negative -1 == 4294967295 because u32",
        4294967295,
        "./third_party/ABY/build/bin/2pc_sub_test",
        {"a": 2, "b": 0},
        {"a": 0, "b": 3},
    ],
    [
        "Multiply two numbers - 1",
        0,
        "./third_party/ABY/build/bin/2pc_mult_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 5},
    ], 
        [
        "Multiply two numbers - 2",
        5,
        "./third_party/ABY/build/bin/2pc_mult_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 5},
    ], 
        [
        "Multiply two numbers - 3",
        10,
        "./third_party/ABY/build/bin/2pc_mult_test",
        {"a": 2, "b": 0},
        {"a": 0, "b": 5},
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value",
        42,
        "./third_party/ABY/build/bin/2pc_mult_add_pub_test",
        {"a": 5, "b": 0, "v": 7},
        {"a": 0, "b": 7, "v": 7},
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value, check only server side public value is added",
        42,
        "./third_party/ABY/build/bin/2pc_mult_add_pub_test",
        {"a": 5, "b": 0, "v": 7},
        {"a": 0, "b": 7, "v": 0},
    ], 
]

arithmetic_boolean_tests = [
    [
        "Test two numbers are equal - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_equals_test",
        {"a": 5, "b": 0},
        {"a": 0, "b": 7},
    ],
    [
        "Test two numbers are equal - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_equals_test",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_than_test",
        {"a": 5, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 2",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_than_test",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int > int - 3",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_than_test",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 1",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_equals_test",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_equals_test",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int >= int - 3",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_equals_test",
        {"a": 6, "b": 0},
        {"a": 0, "b": 7},
    ],
        [
        "Test int < int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_than_test",
        {"a": 7, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Test int < int - 2",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_than_test",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int < int - 3",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_than_test",
        {"a": 2, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int <= int - 1",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_equals_test",
        {"a": 7, "b": 0},
        {"a": 0, "b": 8},
    ], 
    [
        "Test int <= int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_equals_test",
        {"a": 7, "b": 0},
        {"a": 0, "b": 7},
    ], 
    [
        "Test int <= int - 3",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_equals_test",
        {"a": 8, "b": 0},
        {"a": 0, "b": 7},
    ],
    [
        "Test int == int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_equals_test",
        {"a": 7, "b": 0},
        {"a": 0, "b": 8},
    ], 
    [
        "Test int == int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_equals_test",
        {"a": 12, "b": 0},
        {"a": 0, "b": 12},
    ],
]

nary_arithmetic_tests = [
    [
        "Test a + b + c",
        6,
        "./third_party/ABY/build/bin/2pc_nary_arithmetic_add_test",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 2, "c": 3},
    ],
]

bitwise_tests = [
    [
        "Bitwise & - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise & - 2",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise & - 3",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise & - 4",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_and_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise | - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_or_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise | - 2",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise | - 3",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise | - 4",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
        [
        "Bitwise ^ - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_xor_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise ^ - 2",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_xor_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Bitwise ^ - 3",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_xor_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Bitwise ^ - 4",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_xor_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
]

boolean_tests = [
    [
        "Boolean && - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean && - 2",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean && - 3",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean && - 4",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_and_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean || - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_or_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean || - 2",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ],
    [
        "Boolean || - 3",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean || - 4",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean == - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_equals_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 1},
    ],
    [
        "Boolean == - 2",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_equals_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ],
]

nary_boolean_tests = [
    [
        "Test a & b & c - 1",
        0,
        "./third_party/ABY/build/bin/2pc_nary_boolean_and_test",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 1, "c": 0},
    ],
    [
        "Test a & b & c - 2",
        1,
        "./third_party/ABY/build/bin/2pc_nary_boolean_and_test",
        {"a": 1, "b": 0, "c": 0},
        {"a": 0, "b": 1, "c": 1},
    ],
]


const_tests = [
    [
        "Test add client int + server int to const value",
        6,
        "./third_party/ABY/build/bin/2pc_const_arith_test",
        {"a": 2, "b": 0},
        {"a": 0, "b": 3},
    ], 
    [
        "Test server value == const value - 1",
        0,
        "./third_party/ABY/build/bin/2pc_const_bool_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 0},
    ], 
    [
        "Test server value == const value - 2",
        1,
        "./third_party/ABY/build/bin/2pc_const_bool_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 0},
    ], 
]

ite_tests = [
    [
        "Test ite ret bool - 1",
        0,
        "./third_party/ABY/build/bin/2pc_ite_ret_bool_test",
        {"a": 0, "b": 0, "sel": 1},
        {"a": 0, "b": 1, "sel": 1},
    ],
    [
        "Test ite ret bool - 2",
        1,
        "./third_party/ABY/build/bin/2pc_ite_ret_bool_test",
        {"a": 0, "b": 0, "sel": 0},
        {"a": 0, "b": 1, "sel": 0},
    ],
        [
        "Test ite ret int - 1",
        32,
        "./third_party/ABY/build/bin/2pc_ite_ret_int_test",
        {"a": 32, "b": 0, "sel": 1},
        {"a": 0, "b": 45, "sel": 1},
    ],
    [
        "Test ite ret int - 2",
        45,
        "./third_party/ABY/build/bin/2pc_ite_ret_int_test",
        {"a": 32, "b": 0, "sel": 0},
        {"a": 0, "b": 45, "sel": 0},
    ],
]

arr_tests = [
    [
        "Array sum test",
        3,
        "./third_party/ABY/build/bin/2pc_array_sum_test",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Array ret test",
        "2\n1",
        "./third_party/ABY/build/bin/2pc_array_ret_test",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
]

function_tests = [
    [
        "Sum() two numbers - 1",
        3,
        "./third_party/ABY/build/bin/2pc_function_sum_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Sum() two numbers - 2",
        2,
        "./third_party/ABY/build/bin/2pc_function_sum_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 

]

shift_tests = [
     [
        "Left Shift a by 1 - 1",
        20,
        "./third_party/ABY/build/bin/2pc_lhs_test",
        {"a": 10, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Left Shift a by 1 - 2",
        0,
        "./third_party/ABY/build/bin/2pc_lhs_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Left Shift a by 1 - 3",
        0,
        "./third_party/ABY/build/bin/2pc_lhs_test",
        {"a": 2147483648, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Right Shift a by 1 - 1",
        10,
        "./third_party/ABY/build/bin/2pc_rhs_test",
        {"a": 20, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Right Shift a by 1 - 2",
        0,
        "./third_party/ABY/build/bin/2pc_rhs_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 2},
    ], 
]

misc_tests = [
    [
        "Millionaire's problem: server has more money than client",
        0,
        "./third_party/ABY/build/bin/2pc_millionaire_test",
        {"a": 2, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Millionaire's problem: server has equal money to client",
        0,
        "./third_party/ABY/build/bin/2pc_millionaire_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 1},
    ], 
    [
        "Millionaire's problem: server has less money than client",
        1,
        "./third_party/ABY/build/bin/2pc_millionaire_test",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ], 
    [
        "Conversion problem",
        7,
        "./third_party/ABY/build/bin/2pc_conv_test",
        {"a": 0, "b": 0},
        {"a": 0, "b": 7},
    ], 
]

def flatten_args(args: dict) -> list:
    ''' flatten dictionary into list '''
    flat_args = []
    for k, v in args.items():
        flat_args.append(str(k))
        flat_args.append(str(v))
    return flat_args

def build_server_cmd(exec: str, args: dict) -> List[str]:
    return [exec, "-r", "0", "-i"] + flatten_args(args)

def build_client_cmd(exec: str, args: dict) -> List[str]:
    return [exec, "-r", "1", "-i"] + flatten_args(args)

def run_test(desc: str, expected: str, server_cmd: List[str], client_cmd: List[str]) -> bool:
    assert len(server_cmd) > 3, "server cmd does not have enough arguments"
    assert len(client_cmd) > 3, "client cmd does not have enough arguments"

    assert server_cmd[0] == client_cmd[0], "server and client do not have the same cmd: " + server_cmd[0] + ", " + client_cmd[0]

    try:
        server_proc = Popen(server_cmd, stdout=PIPE, stderr=PIPE)
        client_proc = Popen(client_cmd, stdout=PIPE, stderr=PIPE)

        server_out, server_err = server_proc.communicate()
        client_out, client_err = client_proc.communicate()

        assert not server_err, "server cmd has an error"
        assert not client_err, "client cmd has an error"

        server_out = server_out.decode('utf-8').strip()
        client_out = client_out.decode('utf-8').strip()

        assert server_out == client_out, "server out != client out\nserver_out: "+server_out+"\nclient_out: "+client_out
        assert server_out == expected, "output != expected\nserver_out: "+server_out+"\nexpected: "+expected
        return True
    except Exception as e:
        print("Exception: ", e)
        return False

def main():
    # tests will be a list of all tests to run. each element in the list will be 
    # 1. description of test case: string
    # 2. expected output: string
    # 3. executable path: string
    # 4. server arguments: dict[name] = value
    # 5. client arguments: dict[name] = value
    tests = arithmetic_tests + \
        arithmetic_boolean_tests + \
        nary_arithmetic_tests + \
        bitwise_tests + \
        boolean_tests + \
        nary_boolean_tests + \
        const_tests + \
        ite_tests + \
        function_tests + \
        shift_tests + \
        misc_tests
        # arr_tests + \


    failed_test_descs = []
    num_retries = 3
    for test in tests:
        assert len(test) == 5, "test configurations are wrong for test: "+test[0]
        desc = test[0]
        expected = str(test[1])
        path = test[2]
        server_cmd = build_server_cmd(path, test[3])
        client_cmd = build_client_cmd(path, test[4])

        print("Running test:", server_cmd[0])
        print("Description:", desc)

        test_results = []
        for i in range(num_retries):
            test_results.append(run_test(desc, expected, server_cmd, client_cmd))
        
        if any(test_results):
            print("Pass ✅\n")
        else:
            failed_test_descs.append(desc)
            print("Fail 🚫\n")
        
    assert len(failed_test_descs) == 0, "there were failed test cases:\n\t- " + "\n\t- ".join(failed_test_descs)

if __name__ == "__main__":
    main()
