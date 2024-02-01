#!/usr/bin/env python3

import argparse
import subprocess
import sys

from util import *


def log_run_check(cmd):
    s = (
        " ".join(f"'{tok}'" if " " in tok else tok for tok in cmd)
        if type(cmd) == list
        else cmd
    )
    print(f"Running: {s}")
    return subprocess.run(cmd, check=True)


def install(features):
    """
    Used for installing third party libraries

    Parameters
    ----------
        features : set of str
            set of features required
    """

    # install python requirements
    subprocess.run(["pip3", "install", "-r", "requirements.txt"])


def check(features):
    """
    Run cargo check

    Parameters
    ----------
        features : set of str
            set of features required
    """

    cmd = ["cargo", "check", "--tests", "--examples", "--benches", "--bins"]
    if features:
        cmd = cmd + ["--features"] + [",".join(features)]
    log_run_check(cmd)


def check_all():
    """
    Run cargo check with every individual feature
    """
    for feature in cargo_features:
        log_run_check(["cargo", "check", "--tests", "--examples",
                      "--benches", "--bins", "--features", feature])


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
        cmd += ["--" + mode]
    else:
        # default to release mode
        cmd += ["--release"]
    cmd += ["--examples"]

    if features:
        cmd = cmd + ["--features"] + [",".join(features)]

    log_run_check(cmd)

    if "aby" in features:
        if "c" in features:
            log_run_check(["./scripts/build_mpc_c_test.zsh"])
        if "smt" in features and "zok" in features:
            log_run_check(["./scripts/build_mpc_zokrates_test.zsh"])


def test(features, extra_args):
    """
    Run cargo tests and any test cases in the feature list

    Parameters
    ----------
        features : set of str
            set of features required

        extra_args: list of str
            extra arguments to pass to cargo
    """

    build(features)

    test_cmd = ["cargo", "test"]
    test_cmd_release = ["cargo", "test", "--release"]
    if features:
        test_cmd += ["--features"] + [",".join(features)]
        test_cmd_release += ["--features"] + [",".join(features)]
    if len(extra_args) > 0:
        test_cmd += [a for a in extra_args if a != "--"]
        test_cmd_release += [a for a in extra_args if a != "--"]

    log_run_check(test_cmd)
    if load_mode() == "release":
        log_run_check(test_cmd_release)

    if "r1cs" in features and "smt" in features and "datalog" in features:
        log_run_check(["./scripts/test_datalog.zsh"])

    if "zok" in features and "smt" in features:
        if "aby" in features:
            log_run_check(
                ["python3", "./scripts/aby_tests/zokrates_test_aby.py"])
        if "lp" in features:
            log_run_check(["./scripts/test_zok_to_ilp.zsh"])
        if "r1cs" in features:
            if "spartan" in features:  # spartan field
                log_run_check(["./scripts/spartan_zok_test.zsh"])
            else:  # bellman field
                log_run_check(["./scripts/zokrates_test.zsh"])
                if "poly" in features:
                    log_run_check(["./scripts/cp_test.zsh"])
                    log_run_check(["./scripts/ram_test.zsh"])
        if "lp" in features and "r1cs" in features:
            log_run_check(["./scripts/test_zok_to_ilp_pf.zsh"])

    if "c" in features:
        if "aby" in features:
            log_run_check(["python3", "./scripts/aby_tests/c_test_aby.py"])
        if "smt" in features:
            log_run_check(["./scripts/test_c_smt.zsh"])


def benchmark(features):
    mode = load_mode()

    check(features)
    install(features)

    cmd = ["cargo", "build"]
    if mode:
        cmd += ["--" + mode]
    else:
        # default to release mode
        cmd += ["--release"]
    cmd += ["--examples"]

    if features:
        cmd = cmd + ["--features"] + [",".join(features)]
    log_run_check(cmd)


def format():
    print("formatting!")
    log_run_check(["cargo", "fmt", "--all"])


def lint():
    """
    Run cargo clippy

    Parameters
    ----------
        features : set of str
            set of features required
    """
    print("linting!")

    cmd = ["cargo", "clippy", "--tests", "--examples", "--benches", "--bins"]
    if features:
        cmd = cmd + ["--features"] + [",".join(features)]
    log_run_check(cmd)


def flamegraph(features, extra):
    cmd = ["cargo", "flamegraph"]
    if features:
        cmd = cmd + ["--features"] + [",".join(features)]
    cmd += extra
    print("running:", " ".join(cmd))
    log_run_check(cmd)


def clean(features):
    print("cleaning!")
    if "aby" in features:
        log_run_check(["./scripts/clean_aby.zsh"])
    log_run_check(["rm", "-rf", "scripts/aby_tests/__pycache__"])
    log_run_check(
        ["rm", "-rf", "P", "V", "pi", "perf.data perf.data.old flamegraph.svg"]
    )
    log_run_check(["cargo", "clean"])


def set_mode(mode):
    def verify_mode(mode):
        if mode not in ("debug", "release"):
            raise RuntimeError(
                f"Unknown mode: {mode}, --mode <debug, release>")

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
        if f in cargo_features:
            return True
        return False

    features = set(sorted([f for f in features if verify_feature(f)]))
    save_features(features)
    print("Feature set:", sorted(list(features)))
    return features


def format_sub_process_cmd(r: subprocess.CalledProcessError) -> str:
    r.cmd


if __name__ == "__main__":
    try:
        parser = argparse.ArgumentParser()
        parser.add_argument(
            "-i",
            "--install",
            action="store_true",
            help="install all dependencies from the feature set",
        )
        parser.add_argument(
            "-c", "--check", action="store_true", help="run `cargo check`"
        )
        parser.add_argument(
            "--check-all", action="store_true", help="Check all single-feature builds"
        )
        parser.add_argument(
            "-b",
            "--build",
            action="store_true",
            help="run `cargo build` and build all dependencies from the feature set",
        )
        parser.add_argument(
            "-t",
            "--test",
            action="store_true",
            help="build and test all dependencies from the feature set",
        )
        parser.add_argument(
            "-f", "--format", action="store_true", help="run `cargo fmt --all`"
        )
        parser.add_argument(
            "-l", "--lint", action="store_true", help="run `cargo clippy`"
        )
        parser.add_argument(
            "--flamegraph", action="store_true", help="run `cargo flamegraph`"
        )
        parser.add_argument(
            "-C", "--clean", action="store_true", help="remove all generated files"
        )
        parser.add_argument(
            "-m", "--mode", type=str, help="set `debug` or `release` mode"
        )
        parser.add_argument(
            "-A", "--all_features", action="store_true", help="set all features on"
        )
        parser.add_argument(
            "-L", "--list_features", action="store_true", help="print active features"
        )
        parser.add_argument(
            "-F",
            "--features",
            nargs="+",
            help="set features on <aby, c, lp, r1cs, smt, zok>, reset features with -F none",
        )
        parser.add_argument(
            "--benchmark", action="store_true", help="build benchmarks")
        parser.add_argument(
            "extra",
            metavar="PASS_THROUGH_ARGS",
            nargs=argparse.REMAINDER,
            help="Extra arguments for --flamegraph. Prefix with --",
        )
        args = parser.parse_args()

        def verify_single_action(args: argparse.Namespace):
            actions = [
                k
                for k, v in vars(args).items()
                if (type(v) is bool or k in ["features", "mode"]) and bool(v)
            ]
            if len(actions) != 1:
                parser.error(
                    "parser error: only one action can be specified. got: "
                    + " ".join(actions)
                )

        verify_single_action(args)

        def verify_extra_implies_flamegraph_or_test(args: argparse.Namespace):
            if (not args.flamegraph and not args.test) and len(args.extra) > 0:
                parser.error(
                    "parser error: no --flamegraph or --test action, and extra arguments"
                )

        verify_extra_implies_flamegraph_or_test(args)

        features = load_features()

        if args.flamegraph:
            if len(args.extra) > 0 and args.extra[0] == "--":
                del args.extra[0]
            flamegraph(features, args.extra)

        if args.install:
            install(features)

        if args.check:
            check(features)

        if args.check_all:
            check_all()

        if args.build:
            build(features)

        if args.test:
            test(features, args.extra)

        if args.benchmark:
            benchmark(features)

        if args.format:
            format()

        if args.lint:
            lint()

        if args.clean:
            clean(features)

        if args.mode:
            set_mode(args.mode)

        if args.all_features:
            features = set_features(cargo_features)

        if args.list_features:
            print("Feature set:", sorted(list(features)))

        if args.features:
            features = set_features(args.features)
    except subprocess.CalledProcessError as e:
        print("The command")
        cmd_str = " ".join("'" + a + "'" if " " in a else a for a in e.cmd)
        print(f"\t{cmd_str}")
        print(f"failed with exit code {e.returncode}")
        sys.exit(e.returncode)
