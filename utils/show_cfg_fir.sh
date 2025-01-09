#!/bin/sh
./CompileLatte --cfg-fir "$1" | dot -Tsvg | feh - &
cat "$1"
