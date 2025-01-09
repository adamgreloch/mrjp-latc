#!/bin/sh
./latc_llvm --cfg-fir "$1" | dot -Tsvg | feh - &
cat "$1"
