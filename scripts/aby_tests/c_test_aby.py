#!/usr/bin/env python

from util import run_tests
from test_suite import *

if __name__ == "__main__":
    tests = arithmetic_tests + \
        arithmetic_boolean_tests + \
        unsigned_arithmetic_tests + \
        nary_arithmetic_tests + \
        bitwise_tests + \
        boolean_tests + \
        nary_boolean_tests + \
        const_arith_tests + \
        const_bool_tests + \
        ite_tests + \
        shift_tests + \
        div_tests + \
        mod_tests + \
        struct_tests + \
        ptr_tests + \
        c_misc_tests
    # array_tests + \
    # c_array_tests + \
    # matrix_tests + \
    # biomatch_tests + \
    # kmeans_tests + \
    # kmeans_tests_2
    # db_tests
    # gauss_tests + \

    # TODO: add support for return value - int promotion
    # unsigned_arithmetic_tests + \

    run_tests('c', tests)
