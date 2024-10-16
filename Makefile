PYTHON = $(shell command -v python3.11)

LIB_DIR = ./lib
TEST_PASS_DIR = ./test/should-pass
TEST_ERROR_DIR = ./test/should-error

default: tests tests-lib # check_docs 

# Problem regarding the docs: github pages markdown is not compatible
# with using entangled, so the entangled syntax is currently commented
# out. We need a way to automatically put the entangled syntax back in
# and then run deduce on these files. -Jeremy

check_docs: check_index check_fun check_intro check_ref

tests-should-pass:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_PASS_DIR) --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_PASS_DIR) --dir $(LIB_DIR)

tests-should-error:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)


tests-lib: 
	$(PYTHON) ./deduce.py ./lib --recursive-descent --dir $(LIB_DIR)
# List parsing needs to be updated in Deduce.lark
#	$(PYTHON) ./deduce.py . --lalr

tests: tests-should-pass tests-should-error

check_index:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py --recursive-descent index.pf --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr index.pf --dir $(LIB_DIR)

check_fun:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py --recursive-descent FunctionalProgramming.pf --dir $(LIB_DIR)
# List parsing needs to be updated in Deduce.lark
#	$(PYTHON) ./deduce.py --lalr FunctionalProgramming.pf

check_intro:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py --recursive-descent ProofIntro.pf --dir $(LIB_DIR)
# List parsing needs to be updated in Deduce.lark
#	$(PYTHON) ./deduce.py --lalr ProofIntro.pf --dir $(LIB_DIR)

check_ref:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py --recursive-descent Reference.pf --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr Reference.pf --dir $(LIB_DIR)

clean:
	rm -f index.pf FunctionalProgramming.pf ProofIntro.pf
	rm -rf .entangled
