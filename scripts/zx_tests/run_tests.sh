#!/bin/bash

TESTDIR=$(dirname -- "$0")
ZXI=${TESTDIR}/../../target/release/examples/zxi
error=0

echo Running zx should-pass tests:
for i in ${TESTDIR}/*.zx; do
    infile="${i}.in"
    if [[ -a $infile ]]
    then
        output=$(${ZXI} "$i" "$infile")
        if [ "$?" != "0" ]; then
            echo "[failure: should-pass] $i"
            echo "non-zero exit"
            error=1
        else
            outfile="${i}.out"
            if [ $(cat $outfile) != "$output" ]; then
                echo "[failure: should-pass] $i"
                echo "expected output: "
                cat $outfile
                echo "got output: "
                echo "$output"
                error=1
            fi
        fi
    else
        ${ZXI} "$i" &>/dev/null
        if [ "$?" != "0" ]; then
            echo "[failure: should-pass] $i"
            error=1
        fi
    fi
done
echo Done.
echo

echo Running zx should-fail tests:
for i in ${TESTDIR}/*.zxf; do
    localerror=0
    infile="${i}.in"
    if [[ -a $infile ]]
    then
        output=$(${ZXI} "$i" "$infile")
        if [ "$?" != "0" ]; then
            localerror=1
        else
            outfile="${i}.out"
            if [ $(cat $outfile) != "$output" ]; then
                localerror=1
            fi
        fi
        if [ "$localerror" == "0" ]; then
            echo "[failure: should-fail] $i"
            error=1
        fi
    else
        ${ZXI} "$i" &>/dev/null
        if [ "$?" == "0" ]; then
            echo "[failure: should-fail] $i"
            error=1
        fi
    fi
done
echo Done.

exit $error
