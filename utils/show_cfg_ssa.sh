#!/bin/sh
cat "$1"
./latc_llvm --cfg-ssa "$1" | dot -Tsvg | feh -
