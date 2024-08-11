.PHONY: test clean
test:
#	dune build
#	menhir vanilla.mly
	python3.12 syntaxtest.py

clean :
	dune clean
