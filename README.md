# Latte compiler
Compiler written in Haskell without extra dependencies

* Build
```
make
```
* Clean up
```
make clean
```
* Running tests, e.g.
```
./test.sh tests/core latc_llvm
```

## Details

* Latte to LLVM IR compiler
* Translates AST to quadruple called FIR, then to SSA FIR, then to LLVM IR
* Each transformation stage can be peeked at by passing an appropriate flag to
  the compiler (e.g. `--cfg-ssa` will dump SSA CFG in DOT format)
* Optimizations: in progress
* Extensions: in progress
