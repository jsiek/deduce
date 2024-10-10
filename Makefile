PYTHON = $(shell command -v python3.11)

TEST_PASS_DIR = ./test/should-pass
TEST_ERROR_DIR = ./test/should-error

default: tests check_docs tests-lib

check_docs: check_README check_fun check_intro 

tests-should-pass:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_PASS_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_PASS_DIR)

tests-should-error:
	$(PYTHON) ./deduce.py $(TEST_ERROR_DIR) --error


tests-lib: 
	$(PYTHON) ./deduce.py .

tests: tests-should-pass tests-should-error

check_README:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py README.pf

check_fun:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py FunctionalProgramming.pf

check_intro:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py ProofIntro.pf

clean:
	rm -f README.pf FunctionalProgramming.pf ProofIntro.pf
	rm -rf .entangled
