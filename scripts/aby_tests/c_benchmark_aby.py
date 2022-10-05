#!/usr/bin/env python

from util import run_tests
from test_suite import *

if __name__ == "__main__":
    tests = predict_biomatch_tests
        #     kmeans_tests_2 + \
        #     gauss_tests + \
        #     db_tests + \
        #     mnist_tests + \
        #     cryptonets_tests + \
        #     histogram_tests + \
        #     gcd_tests
    run_tests('c', tests)
