#!/usr/bin/env python3

import sys
import os.path
import subprocess as sub

FEATURES = ["ilp", "aby", "seal", "smt", "bellman", "zsharp", "c", "datalog"]
PATH = ".active_features"
DEFAULT_FEATURES = FEATURES

def usage(msg = None):
    print(f"""Usage
feature_manager.py (set|get|default) [FEATURE_LIST]

Commands:
    get: display active features
    set: set active features; requires feature list
    default: set active feature list to default
             these are: {','.join(DEFAULT_FEATURES)}

FEATURE_LIST: a comma-separated list with entries from {','.join(FEATURES)}
""")
    if msg is not None:
        print(f"Error: {msg}")
    sys.exit(2)

def get_feature_path():
    sub.check_output(["git", "rev-parse", "--show-toplevel"], 

def get_features():
    if os.path.exists(

def main():
    if len(sys.argv) < 2:
        usage("No command")
    if sys.argv[1] == "get":
    
        print(os.
