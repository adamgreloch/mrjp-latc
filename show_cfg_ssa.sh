#!/bin/sh
cat "$1"
./CompileLatte -S "$1" | dot -Tsvg | feh -
