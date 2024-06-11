#!/usr/bin/env zsh

set -eu

disable -r time

for file in $(grep -r -l TEST_FILE ${0:a:h:h}/examples | grep -v /gen/)
do
    ${0:a:h}/file_test.py $1 $file
done
