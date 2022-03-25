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
    subprocess.run(cmd, check=True)

def build(features):
    """
    Run cargo build and any test cases in the feature list

    Parameters
    ----------
        features : set of str
            set of features required
    """
    mode = load_mode()

    check(features)
    install(features)

    cmd = ["cargo", "build"] 
    if mode:
        cmd += ["--"+mode] 
    else:
        # default to release mode
        cmd += ["--release"] 
    cmd += ["--examples"]
    
    cargo_features = filter_cargo_features(features)
    if cargo_features:
        cmd = cmd + ["--features"] + cargo_features
    subprocess.run(cmd, check=True)

    if "aby" in features:
        if "c" in features:
            subprocess.run(["./scripts/build_mpc_c_test.zsh"], check=True)
        if "smt" in features and "zok" in features:
            subprocess.run(["./scripts/build_mpc_zokrates_test.zsh"], check=True)
        subprocess.run(["./scripts/build_aby.zsh"], check=True)

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

    if "r1cs" in features and "smt" in features:
        subprocess.run(["./scripts/test_datalog.zsh"], check=True)

    if "zok" in features and "smt" in features:
        if "aby" in features:
            subprocess.run(["python3", "./scripts/aby_tests/zokrates_test_aby.py"], check=True)
        if "lp" in features:
            subprocess.run(["./scripts/test_zok_to_ilp.zsh"], check=True)
        if "r1cs" in features:
            subprocess.run(["./scripts/zokrates_test.zsh"], check=True)
        if "lp" in features and "r1cs" in features:
            subprocess.run(["./scripts/test_zok_to_ilp_pf.zsh"], check=True)

    if "c" in features:
        if "aby" in features:
            subprocess.run(["python3", "./scripts/aby_tests/c_test_aby.py"], check=True)

def format():
    print("formatting!")
    subprocess.run(["cargo", "fmt", "--all"], check=True)

def lint():
    print("linting!")
    subprocess.run(["cargo", "clippy"], check=True)

def flamegraph(features, extra):
    cmd = ["cargo", "flamegraph"]
    cargo_features = filter_cargo_features(features)
    if cargo_features:
        cmd = cmd + ["--features"] + cargo_features
    cmd += extra
    print("running:", " ".join(cmd))
    subprocess.run(cmd, check=True)

def clean(features):
    print("cleaning!")
    if "aby" in features:
        subprocess.run(["./scripts/clean_aby.zsh"])
    subprocess.run(["rm", "-rf", "scripts/aby_tests/__pycache__"])
    subprocess.run(["rm", "-rf", "P", "V", "pi", "perf.data perf.data.old flamegraph.svg"])

def set_mode(mode):
    def verify_mode(mode):
        if mode not in ("debug", "release"):
            raise RuntimeError(f"Unknown mode: {mode}, --mode <debug, release>")
    verify_mode(mode)
    save_mode(mode)

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
    parser.add_argument("--flamegraph", action="store_true", help="run `cargo flamegraph`")
    parser.add_argument("-C", "--clean", action="store_true", help="remove all generated files")
    parser.add_argument("-m", "--mode", type=str, help="set `debug` or `release` mode")
    parser.add_argument("-A", "--all_features", action="store_true", help="set all features on")
    parser.add_argument("-L", "--list_features", action="store_true", help="print active features")
    parser.add_argument("-F", "--features", nargs="+", help="set features on <aby, c, lp, r1cs, smt, zok>, reset features with -F none")
    parser.add_argument("extra", metavar="PASS_THROUGH_ARGS", nargs=argparse.REMAINDER, help="Extra arguments for --flamegraph. Prefix with --")
    args = parser.parse_args()

    def verify_single_action(args: argparse.Namespace):
        actions = [k for k, v in vars(args).items() if (type(v) is bool or k in ["features"]) and bool(v)]
        if len(actions) != 1:
            parser.error("parser error: only one action can be specified. got: " + " ".join(actions))
    verify_single_action(args)

    def verify_extra_implies_flamegraph(args: argparse.Namespace):
        if not args.flamegraph and len(args.extra) > 0:
            parser.error("parser error: no --flamegraph action, and extra arguments")
    verify_extra_implies_flamegraph(args)

    features = load_features()
    set_env(features)

    if args.flamegraph:
        if len(args.extra) > 0 and args.extra[0] == "--":
            del args.extra[0]
        flamegraph(features, args.extra)

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
        clean(features)
    
    if args.mode:
        set_mode(args.mode)

    if args.all_features:
        features = set_features(valid_features)
    
    if args.list_features:
        print("Feature set: ", sorted(list(features)))

    if args.features:
        features = set_features(args.features)
