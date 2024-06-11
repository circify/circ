#!/usr/bin/env python3

import argparse
import re
import os
import subprocess
import sys

from dataclasses import dataclass
from abc import ABC
from typing import Optional

comment_pattern = "(?:;|//|#)"
test_file_pattern = re.compile(rf"{comment_pattern}\s*TEST_FILE")
features_pattern = re.compile(rf"{comment_pattern}\s*FEATURES:\s*(\S[^\n]*\S)")
circ_cmdline_pattern = re.compile(rf"{comment_pattern}\s*CMD:\s*(\S[^\n]*\S)")

# compute the repository root
repo_root = os.path.abspath(os.path.dirname(os.path.realpath(__file__)))
while not os.path.exists(f"{repo_root}/.git") and repo_root != "/":
    repo_root = os.path.abspath(f"{repo_root}/..")
if repo_root == "/":
    print("Not in a git directory")
    sys.exit(1)


@dataclass
class TestConfig(ABC):
    command_templates: list[str]
    features: set[str]


class FileTestResult(ABC):
    pass


@dataclass
class Skipped(FileTestResult):
    missing_features: set[str]


@dataclass
class Fail(FileTestResult):
    command: str
    output: str
    error: str
    exit_code: int


@dataclass
class Pass(FileTestResult):
    pass


@dataclass
class Binaries:
    circ: Optional[str]
    zk: Optional[str]
    cp: Optional[str]


def parse_test_config(path: str) -> TestConfig:
    cfg = TestConfig([], set())
    test_file_found = False
    for line in open(path).readlines():
        if (m := features_pattern.search(line)) is not None:
            cfg.features |= set(m.group(1).replace(",", " ").split(" "))
        elif (m := circ_cmdline_pattern.search(line)) is not None:
            cfg.command_templates.append(m.group(1))
        elif (m := test_file_pattern.search(line)) is not None:
            test_file_found = True
        else:
            pass
    if not test_file_found:
        print(f"Missing TEST_FILE comment in {path}")
        sys.exit(1)
    return cfg


def expand_circ_binaries(cmd: str) -> str:
    for base in ["circ", "cp", "zk"]:
        cmd = re.sub(rf"\${base}\b", f"{repo_root}/target/release/examples/{base}", cmd)
    return cmd


def run_test(features: set[str], path: str) -> FileTestResult:
    path = os.path.abspath(path)
    cfg = parse_test_config(path)
    missing_features = cfg.features - features
    if missing_features:
        return Skipped(missing_features)

    for cmd in cfg.command_templates:
        cmd = cmd.replace("$file", path)
        cmd = expand_circ_binaries(cmd)
        process = subprocess.run(cmd, shell=True, capture_output=True)
        if process.returncode != 0:
            return Fail(
                cmd,
                process.stdout.decode(),
                process.stderr.decode(),
                process.returncode,
            )
    return Pass()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("features", help="comma-separated feature list")
    parser.add_argument("file")
    args = parser.parse_args()
    features = set(args.features.split(","))
    file = args.file
    result = run_test(features, file)
    match result:
        case Pass():
            print(f" passed '{file}'")
        case Fail(command, output, error, exit_code):
            print(f" failed '{file}'")
            print(f"== output ==")
            print(output)
            print(f"== error ==")
            print(error)
            print(f"== exit code ==")
            print(exit_code)
            print(f"== command ==")
            print(command)
            print(f" failed '{file}'")
            sys.exit(1)
        case Skipped(missing_features):
            print(f"skipped '{file}'; missing features {missing_features}")


main()
