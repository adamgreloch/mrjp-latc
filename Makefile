all:
	(cd src && $(MAKE) all)
	mv src/CompileLatte latc_llvm

clean:
	(cd src && $(MAKE) clean)
	-rm -f latc_llvm
