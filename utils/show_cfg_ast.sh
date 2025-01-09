#!/bin/sh
./CompileLatte --cfg-ast "$1" | dot -Tsvg | feh - &
