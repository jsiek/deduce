PYTHON = $(shell command -v python3.11)
DEDUCE = ../deduce.py

LIB_DIR = ../lib

default: check_docs 

# Problem regarding the docs: github pages markdown is not compatible
# with using entangled because it doesn't like spaces in the fenced
# code block language names. So I'm currently using `^` instead of
# spaces and then replacing `^` with a space using sed. -Jeremy

check_docs: check_fun check_intro check_ref

check_fun:
	cat FunctionalProgramming.md | sed 's/deduce\^/deduce /' > FunctionalProgramming.en
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) $(DEDUCE) --recursive-descent FunctionalProgramming.pf --dir $(LIB_DIR)
	$(PYTHON) $(DEDUCE) --lalr FunctionalProgramming.pf --dir $(LIB_DIR)

check_intro:
	cat ProofIntro.md | sed 's/deduce\^/deduce /' > ProofIntro.en
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) $(DEDUCE) --recursive-descent ProofIntro.pf --dir $(LIB_DIR)
	$(PYTHON) $(DEDUCE) --lalr ProofIntro.pf --dir $(LIB_DIR)

check_ref:
	cat Reference.md | sed 's/deduce\^/deduce /' > Reference.en
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) $(DEDUCE) --recursive-descent Reference.pf --dir $(LIB_DIR)
	$(PYTHON) $(DEDUCE) --lalr Reference.pf --dir $(LIB_DIR)

clean:
	rm -f index.pf FunctionalProgramming.pf ProofIntro.pf
	rm -rf .entangled
