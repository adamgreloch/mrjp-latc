#!/bin/sh
./latc_llvm --cfg-ast "$1" | dot -Tsvg | feh - &
