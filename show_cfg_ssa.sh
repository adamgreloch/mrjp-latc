#!/bin/sh
./CompileLatte -S "$1" | dot -Tsvg | feh -
