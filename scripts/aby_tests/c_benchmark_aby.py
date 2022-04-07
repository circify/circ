#!/usr/bin/env python

from util import run_benchmarks
from test_suite import *
import argparse


if __name__ == "__main__":
    
    parser = argparse.ArgumentParser()
    parser.add_argument("-t", "--target", type=str, help="test target")
    parser.add_argument("-s", "--size", type=int, help="size")
    args = parser.parse_args()

    print(args.target)
    print(args.size)
    print(get_tests(args.target, args.size))

    tests = get_tests(args.target, args.size)
    run_benchmarks('c', tests)
