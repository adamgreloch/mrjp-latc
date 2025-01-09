#!/bin/sh
cat "$1"
./latc_llvm --llvm-ir "$1"
