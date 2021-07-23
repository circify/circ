from subprocess import Popen, PIPE
from typing import List

def build_expected(expected) -> str:
    return "output: "+str(expected)

def build_server_cmd(exec: str, args: list) -> List[str]:
    return [exec, "-r", "0", "-i"] + [str(x) for x in args]

def build_client_cmd(exec: str, args: list) -> List[str]:
    return [exec, "-r", "1", "-i"] + [str(x) for x in args]

def run_test(desc: str, expected: str, server_cmd: List[str], client_cmd: List[str]):
    assert len(server_cmd) > 3, "server cmd does not have enough arguments"
    assert len(client_cmd) > 3, "client cmd does not have enough arguments"

    assert server_cmd[0] == client_cmd[0], "server and client do not have the same cmd: " + server_cmd[0] + ", " + client_cmd[0]

    print("Running test:", server_cmd[0])
    print("Description:", desc)
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
        print("Pass ✅\n")
    except:
        print("Fail 🚫\n")

def main():
    # tests will be a list of all tests to run. each element in the list will be 
    # 1. description of test case: string
    # 2. expected output: string
    # 3. executable path: string
    # 4. server arguments: list
    # 5. client arguments: list 
    tests = [
        [
            "Multiply two numbers together",
            10,
            "./third_party/ABY/build/bin/2pc_mult_test",
            [2, 0],
            [0, 5],
        ], 
        [
            "Multiply number with 0",
            0,
            "./third_party/ABY/build/bin/2pc_mult_test",
            [0, 0],
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
        [
            "Millionaire's problem: server has more money than client",
            1,
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
            0,
            "./third_party/ABY/build/bin/2pc_millionaire_test",
            [1, 0],
            [0, 2],
        ], 
        [
            "Boolean equals - 1",
            1,
            "./third_party/ABY/build/bin/2pc_boolean_equals_test",
            [0, 0],
            [0, 0],
        ], 
        [
            "Boolean equals - 2",
            0,
            "./third_party/ABY/build/bin/2pc_boolean_equals_test",
            [1, 0],
            [0, 0],
        ], 
        [
            "Boolean equals - 3",
            0,
            "./third_party/ABY/build/bin/2pc_boolean_equals_test",
            [0, 0],
            [0, 1],
        ], 
        [
            "Boolean equals - 4",
            1,
            "./third_party/ABY/build/bin/2pc_boolean_equals_test",
            [1, 0],
            [0, 1],
        ], 
        [
            "Int equals - 1",
            1,
            "./third_party/ABY/build/bin/2pc_int_equals_test",
            [32, 0],
            [0, 32],
        ], 
        [
            "Int equals - 2",
            0,
            "./third_party/ABY/build/bin/2pc_int_equals_test",
            [1, 0],
            [0, 2],
        ], 
        [
            "Add two numbers",
            3,
            "./third_party/ABY/build/bin/2pc_add_test",
            [1, 0],
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
    ]

    for test in tests:
        assert len(test) == 5, "test configurations are wrong for test: "+test[0]
        desc = test[0]
        expected = build_expected(test[1])
        server_cmd = build_server_cmd(test[2], test[3])
        client_cmd = build_client_cmd(test[2], test[4])
        run_test(desc, expected, server_cmd, client_cmd)

if __name__ == "__main__":
    main()