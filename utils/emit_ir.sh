#!/bin/sh
cat "$1"
./CompileLatte --llvm-ir "$1"
