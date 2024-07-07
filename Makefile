.PHONY: test clean
test:
#	dune build
	python3.12 syntaxtest.py

clean :
	dune clean
