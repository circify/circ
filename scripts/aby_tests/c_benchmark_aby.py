#!/usr/bin/env python

from util import run_tests
from test_suite import *

if __name__ == "__main__":
    tests = db_tests
#             + db_tests \
#             + mnist_tests \
#             + cryptonets_tests
    run_tests('c', tests)
