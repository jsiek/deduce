PYTHON = $(shell command -v python3.13)

LIB_DIR = ./lib
TEST_PASS_DIR = ./test/should-validate
TEST_ERROR_DIR = ./test/should-error
TEST_IMPORT_DIR = ./test/test-imports

default: tests tests-lib

tests-should-validate:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_PASS_DIR) --dir $(LIB_DIR) --dir $(TEST_IMPORT_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_PASS_DIR) --dir $(LIB_DIR) --dir $(TEST_IMPORT_DIR)

tests-should-error:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)

tests-lib: 
	$(PYTHON) ./deduce.py ./lib --recursive-descent --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py ./lib --lalr --dir $(LIB_DIR)

tests: tests-should-validate tests-should-error

tests-compile:
	$(PYTHON) ./test/compile/run_lower.py
	$(PYTHON) ./test/compile/run_e2e.py
	$(PYTHON) ./test/compile/run_determinism.py
	$(PYTHON) ./test/compile/run_headers.py
	$(PYTHON) ./test/compile/run_separate.py
	$(PYTHON) ./test/compile/run_prelude_archive.py

compile-prelude:
	$(PYTHON) ./compiler/compile_prelude.py

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
	cp flags.py deduce
	cp parser.py deduce
	cp proof_checker.py deduce
	cp example.pf deduce
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
	rm -f ./test/compile/lower/*.c ./test/compile/e2e/*.c
	rm -f ./lib/*.c ./lib/*.h ./lib/*.o
	rm -f ./compiler/runtime/libdeduce_prelude.a
	rm -rf ./compiler/runtime/include
