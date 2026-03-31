.PHONY: test clean
test:
#	dune build
#	menhir kete.mly
	python3.12 syntaxtest.py

clean :
	dune clean
