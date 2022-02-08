import os
from os import path
import pickle

# Gloable variables
feature_path = ".features.pkl"
valid_features = {"aby", "c_front"}
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
    with open(feature_path, 'wb') as f:
        pickle.dump(features, f)

def load_features():
    """ Load features from file """
    if path.exists(feature_path):
        with open(feature_path, 'rb') as f:
            return set(sorted(pickle.load(f)))
    else:
        return set()

def set_all_features():
    features = valid_features
    save_features(features)
    return features

def filter_cargo_features(features):
    """ Filter feature list to cargo-specific features """
    return [f for f in features if f in cargo_features]
