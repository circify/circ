#!/bin/bash

TESTDIR=$(dirname -- "$0")
ZXI=${TESTDIR}/../../target/release/examples/zxi
error=0

echo Running zx should-pass tests:
for i in ${TESTDIR}/*.zx; do
    ${ZXI} "$i" &>/dev/null
    if [ "$?" != "0" ]; then
        echo "[failure: should-pass] $i"
        error=1
    fi
done
echo Done.
echo

echo Running zx should-fail tests:
for i in ${TESTDIR}/*.zxf; do
    ${ZXI} "$i" &>/dev/null
    if [ "$?" == "0" ]; then
        echo "[failure: should-fail] $i"
        error=1
    fi
done
echo Done.

exit $error
