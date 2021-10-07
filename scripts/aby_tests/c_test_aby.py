from utils import run_tests
from test_suite import *

if __name__ == "__main__":
    tests = arithmetic_tests + \
        arithmetic_boolean_tests + \
        nary_arithmetic_tests + \
        bitwise_tests + \
        boolean_tests + \
        nary_boolean_tests + \
        const_arith_tests + \
        const_bool_tests + \
        ite_tests + \
        array_tests + \
        c_array_tests
        # loop_tests + \
        # ite_tests + \
        # function_tests + \
        # shift_tests + \
        # misc_tests

    run_tests('c', tests)
