#!/bin/sh
cat "$1"
./CompileLatte --llvm-ir "$1"
lli "${1%lat}bc"
