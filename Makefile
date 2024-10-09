PYTHON = $(shell command -v python3.11)

TEST_PASS_DIR = ./test/should-pass/*.pf
TEST_ERROR_DIR = ./test/should-error/*.pf

default: tests check_docs tests-lib

check_docs: check_README check_fun check_intro 

tests-should-pass:
	for test in $(TEST_PASS_DIR); do \
	  $(PYTHON) ./deduce.py $$test || break; \
	done

tests-should-error:
	for test in $(TEST_ERROR_DIR); do \
	  $(PYTHON) ./deduce.py $$test --error || break; \
	done


tests-lib: 
	for test in ./*.pf; do \
	  $(PYTHON) ./deduce.py $$test || break; \
	done

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
