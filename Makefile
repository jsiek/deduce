PYTHON = $(shell command -v python3.13)

LIB_DIR = ./lib
TEST_PASS_DIR = ./test/should-validate
TEST_ERROR_DIR = ./test/should-error

default: tests tests-lib

tests-should-validate:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_PASS_DIR) --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_PASS_DIR) --dir $(LIB_DIR)

tests-should-error:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)

tests-lib: 
	$(PYTHON) ./deduce.py ./lib --recursive-descent --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py ./lib --lalr --dir $(LIB_DIR)

tests: tests-should-validate tests-should-error

package:
	$(PYTHON) ./deduce.py ./lib
	mkdir deduce
	cp -r lib deduce
	cp abstract_syntax.py deduce
	cp alist.py deduce
	cp Deduce.lark deduce
	cp deduce.py deduce
	cp edit_distance.py deduce
	cp error.py deduce
	cp parser.py deduce
	cp proof_checker.py deduce
	cp README.md deduce
	cp rec_desc_parser.py deduce
	zip "deduce-release" -r deduce
	rm -rf deduce
	rm -f ./lib/*.thm

clean:
	rm -f *~ ./lib/*~ ./test/should-validate/*~ ./test/should-error/*~
	rm -f ./lib/*.thm
	rm -f ./test/should-validate/*.thm
	rm -f deduce-release.zip
