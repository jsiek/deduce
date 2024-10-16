PYTHON = $(shell command -v python3.11)

LIB_DIR = ./lib
TEST_PASS_DIR = ./test/should-pass
TEST_ERROR_DIR = ./test/should-error

default: tests tests-lib

tests-should-pass:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_PASS_DIR) --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_PASS_DIR) --dir $(LIB_DIR)

tests-should-error:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)

tests-lib: 
	$(PYTHON) ./deduce.py ./lib --recursive-descent --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py ./lib --lalr --dir $(LIB_DIR)

tests: tests-should-pass tests-should-error

