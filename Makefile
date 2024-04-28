.PHONY: test
test:
	dune build
	python3.12 syntaxtest.py
