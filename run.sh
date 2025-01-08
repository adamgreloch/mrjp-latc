#!/bin/sh
cat "$1"
./CompileLatte -l "$1"
lli "${1%lat}bc"
