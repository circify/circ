#!/usr/bin/env python

from utils import run_tests
from test_suite import *

if __name__ == "__main__":
    tests =  [[
        "loop add",
        3,
        "./third_party/ABY/build/bin/2pc_loop_add",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ]]

    run_tests('c', tests)
