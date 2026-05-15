PYTHON = $(shell command -v python3.13)

LIB_DIR = ./lib
TEST_PASS_DIR = ./test/should-validate
TEST_ERROR_DIR = ./test/should-error
TEST_IMPORT_DIR = ./test/test-imports
EXAMPLES_DIR = ./examples

default: static tests-tokens tests

static:
	$(PYTHON) -m ruff check .
	$(PYTHON) -m mypy .

tests-tokens:
	$(PYTHON) ./gh_pages/scripts/keywords.py
	$(PYTHON) ./gh_pages/scripts/reference_grammar.py

# Fast parallel in-process sweep. ``test-deduce.py`` runs the default
# regression categories (cli + lib + should-validate + test/prelude +
# should-error with ``.err`` diff). It pays the prelude bootstrap
# once in the parent and forks worker processes that inherit the
# populated AST cache via copy-on-write -- ~10x faster than the
# previous subprocess-per-file harness.
tests: static
	$(PYTHON) test-deduce.py

# Per-category targets kept for granular debugging; ``make tests``
# above is the fast all-in-one entry point.
tests-should-validate:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_PASS_DIR) --dir $(LIB_DIR) --dir $(TEST_IMPORT_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_PASS_DIR) --dir $(LIB_DIR) --dir $(TEST_IMPORT_DIR)

tests-should-error:
	$(PYTHON) ./deduce.py --recursive-descent $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py --lalr $(TEST_ERROR_DIR) --error --dir $(LIB_DIR)

tests-lib:
	$(PYTHON) ./deduce.py ./lib --recursive-descent --dir $(LIB_DIR)
	$(PYTHON) ./deduce.py ./lib --lalr --dir $(LIB_DIR)

tests-examples:
	$(PYTHON) ./deduce.py --recursive-descent $(EXAMPLES_DIR)
	$(PYTHON) ./deduce.py --lalr $(EXAMPLES_DIR)

# A curated subset of LSP / diagnostic-handling tests for rapid
# iteration on the error.py + check_deduce sink machinery. These are
# the cases most sensitive to changes in raise/record semantics:
# spurious-diagnostic regressions on valid files, multi-hole shape,
# the PTuple "comma proves" speculative-comma trap, the shape of an
# IncompleteProof diagnostic, and a few representative should-error
# fixtures spanning incomplete / type-error / overload-conflict
# shapes. Runs in a few seconds; the full LSP suite takes ~3 minutes.
quick-lsp:
	$(PYTHON) -m pytest test/lsp/test_check.py test/lsp/test_check_proofs_cache.py \
	    -k "valid_files \
	        or incomplete_proof_diagnostic \
	        or multiple_holes \
	        or proof_error_plus_hole \
	        or editing_T1_invalidates \
	        or advice_and.pf \
	        or overload6.pf \
	        or apply_to_non_imp.pf \
	        or forgot_def \
	        or missing_recall.pf \
	        or recursive_clause_name_mismatch.pf"

# Full LSP suite (~3:20). Use ``quick-lsp`` for fast iteration; this
# target is the comprehensive check before merging.
tests-lsp:
	$(PYTHON) -m pytest test/lsp/

# Python-level unit tests for AST helpers (issue #475). Fast: runs in
# under a second. Hand-built AST specimens exercise ``__eq__`` /
# ``copy`` / field-completeness so a regression points at the
# offending method directly rather than at a downstream ``.pf`` diff.
tests-unit:
	$(PYTHON) -m pytest test/unit/

quick-tests: 
	$(PYTHON) ./deduce.py --recursive-descent lib/Nat.pf --dir $(LIB_DIR) --dir $(TEST_IMPORT_DIR)
	$(PYTHON) ./deduce.py --recursive-descent ./test/should-error/induction2.pf --error --dir $(LIB_DIR)

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
