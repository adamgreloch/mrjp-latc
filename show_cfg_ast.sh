#!/bin/sh
./CompileLatte -g "$1" | dot -Tsvg | feh - &
