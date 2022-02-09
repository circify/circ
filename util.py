import os
from os import path

# Gloable variables
feature_path = ".features.txt"
valid_features = {"aby", "c_front", "none"}
cargo_features = {"c_front"}

# Environment variables
ABY_SOURCE="./../ABY"

def set_env(features):
    for f in features:
        if f in ('aby'):
            if not os.getenv("ABY_SOURCE"):
                os.environ["ABY_SOURCE"] = ABY_SOURCE

def save_features(features):
    """ Save features to file """
    with open(feature_path, 'w') as f:
        feature_str = "\n".join(sorted(features))
        f.write(feature_str)

def load_features():
    """ Load features from file """
    if path.exists(feature_path):
        with open(feature_path, 'r') as f:
            features = f.read().splitlines()
            return set(sorted(features))
    else:
        return set()

def filter_cargo_features(features):
    """ Filter feature list to cargo-specific features """
    return [f for f in features if f in cargo_features]
