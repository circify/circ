import os
from os import path

# Gloable variables
feature_path = ".features.txt"
mode_path = ".mode.txt"

# TODO: add in "kahip", "kahypar" binaries dependencies when adding new MPC changes
cargo_features = {"aby", "c", "lp", "r1cs", "smt",
                  "zok", "datalog", "bellman", "spartan", "poly"}


def save_mode(mode):
    """ Save mode to file """
    with open(mode_path, 'w') as f:
        f.write(mode)


def load_mode():
    """ Load mode from file """
    if path.exists(mode_path):
        with open(mode_path, 'r') as f:
            return f.read().strip()
    else:
        return ""


def save_features(features):
    """ Save features to file """
    with open(feature_path, 'w') as f:
        feature_str = "\n".join(features)
        f.write(feature_str)


def load_features():
    """ Load features from file """
    if path.exists(feature_path):
        with open(feature_path, 'r') as f:
            features = f.read().splitlines()
            return features
    else:
        return []
