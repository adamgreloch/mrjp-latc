all:
	(cd src && $(MAKE) all)
	mv src/CompileLatte latc_llvm
	cp latc_llvm latc

clean:
	(cd src && $(MAKE) clean)
	-rm -f latc_llvm latc
