import os
from os import path

# Gloable variables
feature_path = ".features.txt"
mode_path = ".mode.txt"
valid_features = {"aby", "bench", "c", "lp", "r1cs", "smt", "zok"}
cargo_features = {"bench", "c", "lp", "r1cs", "smt", "zok"}

# Environment variables
ABY_SOURCE = "./../ABY"
KAHIP_SOURCE = "./../KaHIP"
KAHYPAR_SOURCE = "./../kahypar"


def set_env(features):
    for f in features:
        if f == 'aby':
            if not os.getenv("ABY_SOURCE"):
                os.environ["ABY_SOURCE"] = ABY_SOURCE
            if not os.getenv("KAHIP_SOURCE"):
                os.environ["KAHIP_SOURCE"] = KAHIP_SOURCE
            if not os.getenv("KAHYPAR_SOURCE"):
                os.environ["KAHYPAR_SOURCE"] = KAHYPAR_SOURCE


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
            return set(features)
    else:
        return set()


def filter_cargo_features(features):
    """ Filter feature list to cargo-specific features """
    return [" ".join([f for f in features if f in cargo_features])]
