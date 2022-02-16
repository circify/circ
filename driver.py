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
        if f == "aby":
            if verify_path_empty(ABY_SOURCE):
                subprocess.run(["git", "clone", "https://github.com/edwjchen/ABY.git", ABY_SOURCE])
                subprocess.run(["./scripts/build_aby.zsh"])

            # Get EZPC header file
            subprocess.run(["mkdir", "-p", EZPC_SOURCE])
            subprocess.run(["wget", "-O", EZPC_SOURCE+"/ezpc.h", "https://raw.githubusercontent.com/circify/circ/master/third_party/EZPC/ezpc.h"])


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

    if "aby" in features:
        if "c_front" in features:
            subprocess.run(["./scripts/build_mpc_c_test.zsh"])
        if "smt" in features and "zok_front" in features:
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

    test_cmd = ["cargo", "test"]
    cargo_features = filter_cargo_features(features)
    if cargo_features:
        test_cmd = test_cmd + ["--features"] + cargo_features
    subprocess.run(test_cmd, check=True)

    if "c_front" in features:
        if "a" in features:
            subprocess.run(["python3", "./scripts/aby_tests/c_test_aby.py"], check=True)

    if "r1cs" in features and "smt" in features:
        subprocess.run(["./scripts/test_datalog.zsh"], check=True)

    if "zok_front" in features and "smt" in features:
        if "aby" in features:
            subprocess.run(["python3", "./scripts/aby_tests/zokrates_test_aby.py"], check=True)
        if "lp" in features:
            subprocess.run(["./scripts/test_zok_to_ilp.zsh"], check=True)
        if "r1cs" in features:
            subprocess.run(["./scripts/zokrates_test.zsh"], check=True)
        if "lp" in features and "r1cs" in features:
            subprocess.run(["./scripts/test_zok_to_ilp_pf.zsh"], check=True)

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
    # reset features
    if "none" in features:
        features = set()

    def verify_feature(f):
        if f in valid_features:
            return True
        return False
    features = set(sorted([f for f in features if verify_feature(f)]))
    save_features(features)
    print("Feature set:", sorted(list(features)))
    return features 

if __name__ == "__main__":
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
    parser.add_argument("-F", "--features", nargs="+", help="set features on <aby, c_front, lp, r1cs, smt, zok_front>, reset features with -F none")
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
        print("Feature set: ", sorted(list(features)))

    if args.features:
        features = set_features(args.features)