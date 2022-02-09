#!/usr/bin/env python3

import argparse
import subprocess

from util import *

def install(features):
    """
    Used for installing third party libraries

    Parameters
    ----------
        features : set of str
            set of features required
    """

    def verify_path_empty(path) -> bool:
        return not os.path.isdir(path) or (os.path.isdir(path) and not os.listdir(path)) 

    for f in features:
        if f == 'aby':
            if verify_path_empty(ABY_SOURCE):
                subprocess.run(["git", "clone", "https://github.com/edwjchen/ABY.git", ABY_SOURCE])

def check(features):
    """
    Run cargo check

    Parameters
    ----------
        features : set of str
            set of features required
    """

    cmd = ["cargo", "check"]

    cargo_features = filter_cargo_features(features)
    if cargo_features:        
       cmd = cmd + ["--features"] + cargo_features

    subprocess.run(cmd)

def build(features):
    """
    Run cargo build and any test cases in the feature list

    Parameters
    ----------
        features : set of str
            set of features required
    """
    
    check(features)
    install(features)

    release_cmd = ["cargo", "build", "--release", "--examples"]
    cmd = ["cargo", "build", "--examples"]

    cargo_features = filter_cargo_features(features)
    if cargo_features:
        release_cmd = release_cmd + ["--features"] + cargo_features
        cmd = cmd + ["--features"] + cargo_features

    subprocess.run(release_cmd)
    subprocess.run(cmd)

    for f in features: 
        if f == 'aby':
            if 'c_front' in features:
                subprocess.run(["./scripts/build_mpc_c_test.zsh"])
            subprocess.run(["./scripts/build_mpc_zokrates_test.zsh"])
            subprocess.run(["./scripts/build_aby.zsh"])

def test(features):
    """
    Run cargo tests and any test cases in the feature list

    Parameters
    ----------
        features : set of str
            set of features required
    """

    build(features)

    subprocess.run(["cargo", "test"], check=True)
    subprocess.run(["./scripts/zokrates_test.zsh"], check=True)
    subprocess.run(["./scripts/test_zok_to_ilp.zsh"], check=True)
    subprocess.run(["./scripts/test_zok_to_ilp_pf.zsh"], check=True)
    subprocess.run(["./scripts/test_datalog.zsh"], check=True)
    subprocess.run(["python3", "./scripts/aby_tests/zokrates_test_aby.py"], check=True)

    for f in features: 
        if f == 'aby':
            if 'c_front' in features:
                subprocess.run(["python3", "./scripts/aby_tests/c_test_aby.py"], check=True)

def format():
    print("formatting!")
    subprocess.run(["cargo", "fmt", "--all"], check=True)

def lint():
    print("linting!")
    subprocess.run(["cargo", "clippy"], check=True)

def clean():
    print("cleaning!")
    subprocess.run(["./scripts/clean_aby.zsh"])
    subprocess.run(["rm", "-rf", "scripts/aby_tests/__pycache__"])
    subprocess.run(["rm", "-rf", "P", "V", "pi", "perf.data perf.data.old flamegraph.svg"])

def set_features(features):
    """
    Filter invalid features and save features to a file.

    Parameters
    ----------
        features : set of str
            set of features required
    """
    def verify_feature(f):
        if f in valid_features:
            return True
        return False
    features = set(sorted([f for f in features if verify_feature(f)]))
    
    # reset features
    if 'none' in features:
        features = set()

    print("Feature set:", features)
    save_features(features)
    return features 

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--install", action="store_true", help="install all dependencies from the feature set")
    parser.add_argument("-c", "--check", action="store_true", help="run `cargo check`")
    parser.add_argument("-b", "--build", action="store_true", help="run `cargo build` and build all dependencies from the feature set")
    parser.add_argument("-t", "--test", action="store_true", help="build and test all dependencies from the feature set")
    parser.add_argument("-f", "--format", action="store_true", help="run `cargo fmt --all`")
    parser.add_argument("-l", "--lint", action="store_true", help="run `cargo clippy`")
    parser.add_argument("-C", "--clean", action="store_true", help="remove all generated files")
    parser.add_argument("-A", "--all_features", action="store_true", help="set all features on")
    parser.add_argument("-L", "--list_features", action="store_true", help="print active features")
    parser.add_argument("-F", "--features", nargs="+", help="set features on, reset features with -F none")
    args = parser.parse_args()

    def verify_single_action(args: argparse.Namespace):
        if [bool(v) for v in vars(args).values()].count(True) != 1:
            parser.error("parser error: only one action can be specified")
    verify_single_action(args)

    features = load_features()
    set_env(features)

    if args.install:
        install(features)

    if args.check:
        check(features)

    if args.build:
        build(features)

    if args.test:
        test(features)

    if args.format:
        format()

    if args.lint:
        lint()

    if args.clean:
        clean()
    
    if args.all_features:
        features = set_features(valid_features)
    
    if args.list_features:
        print(features)

    if args.features:
        features = set_features(args.features)