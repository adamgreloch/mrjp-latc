#!/bin/sh
./CompileLatte -f "$1" | dot -Tsvg | feh - &
cat "$1"
