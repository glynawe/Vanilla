.PHONY: test clean
test:
#	dune build
	python3.12 syntaxtest.py
	python3.12 syntaxtest2.py

clean :
	dune clean
