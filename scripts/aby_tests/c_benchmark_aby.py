#!/usr/bin/env python

from util import run_tests
from test_suite import *

if __name__ == "__main__":
    tests = cryptonets_tests
    run_tests('c', tests)
