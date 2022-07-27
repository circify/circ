#!/usr/bin/env python

from util import run_tests
from test_suite import *

if __name__ == "__main__":
    tests = kmeans_tests_2
    run_tests('c', tests)
