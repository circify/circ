#!/usr/bin/env python3

from util import run_benchmarks
from test_suite import *

if __name__ == "__main__":
    tests = benchmark_tests
    run_benchmarks('c', tests)
