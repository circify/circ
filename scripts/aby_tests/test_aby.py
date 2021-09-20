from subprocess import Popen, PIPE
import sys
from typing import List
import time 

from test_suite import *


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
        # print("Exception: ", e)
        return False


def init_progress_bar(toolbar_width=40):
    print("Running ABY unit tests")
    sys.stdout.write("[%s]" % (" " * toolbar_width))
    sys.stdout.flush()
    sys.stdout.write("\b" * (toolbar_width+1)) 

def update_progress_bar():
    sys.stdout.write("=")
    sys.stdout.flush()

def end_progress_bar():
    sys.stdout.write("\n") # this ends the progress bar

def main():
    # tests will be a list of all tests to run. each element in the list will be 
    # 1. description of test case: string
    # 2. expected output: string
    # 3. executable path: string
    # 4. server arguments: dict[name] = value
    # 5. client arguments: dict[name] = value
    tests = arithmetic_tests # + \
        # arithmetic_boolean_tests + \
        # nary_arithmetic_tests + \
        # bitwise_tests + \
        # boolean_tests + \
        # nary_boolean_tests + \
        # const_tests + \
        # loop_tests + \
        # ite_tests + \
        # function_tests + \
        # shift_tests + \
        # misc_tests
        # arr_tests + \


    failed_test_descs = []
    num_retries = 3
    progress_inc = 5
    init_progress_bar(len(tests) // progress_inc + 1)
    for t, test in enumerate(tests):
        assert len(test) == 5, "test configurations are wrong for test: "+test[0]
        desc = test[0]
        expected = str(test[1])
        path = test[2]
        server_cmd = build_server_cmd(path, test[3])
        client_cmd = build_client_cmd(path, test[4])

        test_results = []
        for i in range(num_retries):
            test_results.append(run_test(desc, expected, server_cmd, client_cmd))
        
        if not any(test_results):
            failed_test_descs.append(desc)

        if t % progress_inc == 0:
            update_progress_bar()
    end_progress_bar()
    
    if len(failed_test_descs) == 0:
        print("All tests passed ✅")

    assert len(failed_test_descs) == 0, "there were failed test cases:\n\t- " + "\n\t- ".join(failed_test_descs)

if __name__ == "__main__":
    main()
