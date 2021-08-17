from subprocess import Popen, PIPE
from typing import List

arithmetic_tests = [
    [
        "Add two numbers - 1",
        3,
        "./third_party/ABY/build/bin/2pc_add_test",
        [1, 0],
        [0, 2],
    ], 
    [
        "Add two numbers - 2",
        2,
        "./third_party/ABY/build/bin/2pc_add_test",
        [0, 0],
        [0, 2],
    ], 
    [
        "Subtract two numbers",
        1,
        "./third_party/ABY/build/bin/2pc_sub_test",
        [3, 0],
        [0, 2],
    ], 
    [
        "Subtract two numbers, negative -1 == 4294967295 because u32",
        4294967295,
        "./third_party/ABY/build/bin/2pc_sub_test",
        [2, 0],
        [0, 3],
    ],
    [
        "Multiply two numbers - 1",
        0,
        "./third_party/ABY/build/bin/2pc_mult_test",
        [0, 0],
        [0, 5],
    ], 
        [
        "Multiply two numbers - 2",
        5,
        "./third_party/ABY/build/bin/2pc_mult_test",
        [1, 0],
        [0, 5],
    ], 
        [
        "Multiply two numbers - 3",
        10,
        "./third_party/ABY/build/bin/2pc_mult_test",
        [2, 0],
        [0, 5],
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value",
        42,
        "./third_party/ABY/build/bin/2pc_mult_add_pub_test",
        [5, 0, 7],
        [0, 7, 7],
    ], 
    [
        # only server side public value works 
        "Multiply two numbers together and add with public value, check only server side public value is added",
        42,
        "./third_party/ABY/build/bin/2pc_mult_add_pub_test",
        [5, 0, 7],
        [0, 7, 0],
    ], 
]

arithmetic_boolean_tests = [
    [
        "Test two numbers are equal - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_equals_test",
        [5, 0],
        [0, 7],
    ],
    [
        "Test two numbers are equal - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_equals_test",
        [7, 0],
        [0, 7],
    ], 
    [
        "Test int > int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_than_test",
        [5, 0],
        [0, 7],
    ], 
    [
        "Test int > int - 2",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_than_test",
        [7, 0],
        [0, 7],
    ], 
    [
        "Test int > int - 3",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_than_test",
        [8, 0],
        [0, 7],
    ], 
    [
        "Test int >= int - 1",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_equals_test",
        [8, 0],
        [0, 7],
    ], 
    [
        "Test int >= int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_greater_equals_test",
        [7, 0],
        [0, 7],
    ], 
    [
        "Test int >= int - 3",
        0,
        "./third_party/ABY/build/bin/2pc_int_greater_equals_test",
        [6, 0],
        [0, 7],
    ],
        [
        "Test int < int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_than_test",
        [7, 0],
        [0, 2],
    ], 
    [
        "Test int < int - 2",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_than_test",
        [7, 0],
        [0, 7],
    ], 
    [
        "Test int < int - 3",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_than_test",
        [2, 0],
        [0, 7],
    ], 
    [
        "Test int <= int - 1",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_equals_test",
        [7, 0],
        [0, 8],
    ], 
    [
        "Test int <= int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_less_equals_test",
        [7, 0],
        [0, 7],
    ], 
    [
        "Test int <= int - 3",
        0,
        "./third_party/ABY/build/bin/2pc_int_less_equals_test",
        [8, 0],
        [0, 7],
    ],
    [
        "Test int == int - 1",
        0,
        "./third_party/ABY/build/bin/2pc_int_equals_test",
        [7, 0],
        [0, 8],
    ], 
    [
        "Test int == int - 2",
        1,
        "./third_party/ABY/build/bin/2pc_int_equals_test",
        [12, 0],
        [0, 12],
    ],
]

nary_arithmetic_tests = [
    [
        "Test a + b + c",
        6,
        "./third_party/ABY/build/bin/2pc_nary_arithmetic_add_test",
        [1, 0, 0],
        [0, 2, 3],
    ],
]

bitwise_tests = [
    [
        "Bitwise & - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and_test",
        [0, 0],
        [0, 0],
    ],
    [
        "Bitwise & - 2",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and_test",
        [1, 0],
        [0, 0],
    ],
    [
        "Bitwise & - 3",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_and_test",
        [0, 0],
        [0, 1],
    ],
    [
        "Bitwise & - 4",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_and_test",
        [1, 0],
        [0, 1],
    ],
    [
        "Bitwise | - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_or_test",
        [0, 0],
        [0, 0],
    ],
    [
        "Bitwise | - 2",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or_test",
        [1, 0],
        [0, 0],
    ],
    [
        "Bitwise | - 3",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or_test",
        [0, 0],
        [0, 1],
    ],
    [
        "Bitwise | - 4",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_or_test",
        [1, 0],
        [0, 1],
    ],
        [
        "Bitwise ^ - 1",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_xor_test",
        [0, 0],
        [0, 0],
    ],
    [
        "Bitwise ^ - 2",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_xor_test",
        [1, 0],
        [0, 0],
    ],
    [
        "Bitwise ^ - 3",
        1,
        "./third_party/ABY/build/bin/2pc_bitwise_xor_test",
        [0, 0],
        [0, 1],
    ],
    [
        "Bitwise ^ - 4",
        0,
        "./third_party/ABY/build/bin/2pc_bitwise_xor_test",
        [1, 0],
        [0, 1],
    ],
]

boolean_tests = [
    [
        "Boolean && - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and_test",
        [0, 0],
        [0, 0],
    ],
    [
        "Boolean && - 2",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and_test",
        [1, 0],
        [0, 0],
    ],
    [
        "Boolean && - 3",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_and_test",
        [0, 0],
        [0, 1],
    ],
    [
        "Boolean && - 4",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_and_test",
        [1, 0],
        [0, 1],
    ],
    [
        "Boolean || - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_or_test",
        [0, 0],
        [0, 0],
    ],
    [
        "Boolean || - 2",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or_test",
        [1, 0],
        [0, 0],
    ],
    [
        "Boolean || - 3",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or_test",
        [0, 0],
        [0, 1],
    ],
    [
        "Boolean || - 4",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_or_test",
        [1, 0],
        [0, 1],
    ],
    [
        "Boolean == - 1",
        0,
        "./third_party/ABY/build/bin/2pc_boolean_equals_test",
        [0, 0],
        [0, 1],
    ],
    [
        "Boolean == - 2",
        1,
        "./third_party/ABY/build/bin/2pc_boolean_equals_test",
        [1, 0],
        [0, 1],
    ],
]

nary_boolean_tests = [
    [
        "Test a & b & c - 1",
        0,
        "./third_party/ABY/build/bin/2pc_nary_boolean_and_test",
        [1, 0, 0],
        [0, 1, 0],
    ],
    [
        "Test a & b & c - 2",
        1,
        "./third_party/ABY/build/bin/2pc_nary_boolean_and_test",
        [1, 0, 0],
        [0, 1, 1],
    ],
]

const_tests = [
    [
        "Test add client int + server int to const value",
        6,
        "./third_party/ABY/build/bin/2pc_const_arith_test",
        [2, 0],
        [0, 3],
    ], 
    [
        "Test server value == const value - 1",
        0,
        "./third_party/ABY/build/bin/2pc_const_bool_test",
        [0, 0],
        [0, 0],
    ], 
    [
        "Test server value == const value - 2",
        1,
        "./third_party/ABY/build/bin/2pc_const_bool_test",
        [1, 0],
        [0, 0],
    ], 
]


misc_tests = [
    [
        "Millionaire's problem: server has more money than client",
        0,
        "./third_party/ABY/build/bin/2pc_millionaire_test",
        [2, 0],
        [0, 1],
    ], 
    [
        "Millionaire's problem: server has equal money to client",
        0,
        "./third_party/ABY/build/bin/2pc_millionaire_test",
        [1, 0],
        [0, 1],
    ], 
    [
        "Millionaire's problem: server has less money than client",
        1,
        "./third_party/ABY/build/bin/2pc_millionaire_test",
        [1, 0],
        [0, 2],
    ], 
]

def build_expected(expected) -> str:
    return "output: "+str(expected)

def build_server_cmd(exec: str, args: list) -> List[str]:
    return [exec, "-r", "0", "-i"] + [str(x) for x in args]

def build_client_cmd(exec: str, args: list) -> List[str]:
    return [exec, "-r", "1", "-i"] + [str(x) for x in args]

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

        assert server_out.startswith("output: "), "server output did not start with \"output:\", but instead with: "+server_out
        assert client_out.startswith("output: "), "client output did not start with \"output:\", but instead with: "+client_out
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
    # 4. server arguments: list
    # 5. client arguments: list 
    tests = arithmetic_tests + \
        arithmetic_boolean_tests + \
        nary_arithmetic_tests + \
        bitwise_tests + \
        boolean_tests + \
        nary_boolean_tests + \
        const_tests + \
        misc_tests
        

    failed_test_descs = []
    num_retries = 3
    for test in tests:
        assert len(test) == 5, "test configurations are wrong for test: "+test[0]
        desc = test[0]
        expected = build_expected(test[1])
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
