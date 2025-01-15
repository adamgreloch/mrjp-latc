#!/bin/sh
cat "$1"
./latc_llvm --cfg-gcse "$1" | dot -Tsvg | feh -
