from utils import *
from zokrates_test_suite import *

def run_tests():
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
        const_arith_tests + \
        const_bool_tests + \
        loop_tests + \
        ite_tests + \
        function_tests + \
        shift_tests + \
        misc_tests
        # arr_tests + \

    failed_test_descs = []
    num_retries = 3
    progress_inc = 5
    init_progress_bar(len(tests) // progress_inc)
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
    run_tests()
