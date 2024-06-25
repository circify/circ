#!/usr/bin/env zsh
set -e
default_features_line=$(grep 'default = ' ${0:a:h:h}/Cargo.toml)
if [[ $default_features_line != "default = []" ]]
then
    echo "There are default features in Cargo.toml"
    echo
    echo $default_features_line
    echo
    echo "Please remove them before pushing"
    exit 1
fi
