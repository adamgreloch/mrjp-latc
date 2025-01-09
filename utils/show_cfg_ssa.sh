#!/bin/sh
cat "$1"
./CompileLatte --cfg-ssa "$1" | dot -Tsvg | feh -
