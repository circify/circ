#!/usr/bin/env python

import os
from utils import run_tests
from test_suite import *

ABY_SOURCE = os.getenv("ABY_SOURCE")

if __name__ == "__main__":
    tests =  [[
        "loop add",
        3,
        ABY_SOURCE+"/build/bin/2pc_loop_add",
        {"a": 1, "b": 0},
        {"a": 0, "b": 2},
    ]]

    run_tests('c', tests)
