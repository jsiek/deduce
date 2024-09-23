PYTHON=/opt/homebrew/bin/python3.10

default: tests check_docs

check_docs: check_README check_fun check_intro 

tests: 
	$(PYTHON) ./deduce.py test/theorem_true.pf
	$(PYTHON) ./deduce.py test/theorem_true_error.pf --error
	$(PYTHON) ./deduce.py test/theorem_false1.pf
	$(PYTHON) ./deduce.py test/theorem_false2.pf
	$(PYTHON) ./deduce.py test/theorem_false3.pf
	$(PYTHON) ./deduce.py test/theorem_let.pf
	$(PYTHON) ./deduce.py test/theorem_and.pf
	$(PYTHON) ./deduce.py test/theorem_and2.pf
	$(PYTHON) ./deduce.py test/theorem_and3.pf
	$(PYTHON) ./deduce.py test/theorem_and4.pf
	$(PYTHON) ./deduce.py test/theorem_and5.pf --error
	$(PYTHON) ./deduce.py test/theorem_and6.pf --error
	$(PYTHON) ./deduce.py test/theorem_implies.pf
	$(PYTHON) ./deduce.py test/theorem_implies2.pf
	$(PYTHON) ./deduce.py test/theorem_implies3.pf
	$(PYTHON) ./deduce.py test/theorem_implies4.pf
	$(PYTHON) ./deduce.py test/theorem_implies5.pf --error
	$(PYTHON) ./deduce.py test/theorem_implies6.pf --error
	$(PYTHON) ./deduce.py test/theorem_or.pf
	$(PYTHON) ./deduce.py test/theorem_or2.pf
	$(PYTHON) ./deduce.py test/theorem_or3.pf --error
	$(PYTHON) ./deduce.py test/theorem_or4.pf --error
	$(PYTHON) ./deduce.py test/suffices1.pf
	$(PYTHON) ./deduce.py test/suffices_def.pf
	$(PYTHON) ./deduce.py test/suffices_rewrite.pf
	$(PYTHON) ./deduce.py test/switch_term.pf
	$(PYTHON) ./deduce.py test/switch_term_error.pf --error
	$(PYTHON) ./deduce.py test/rec1.pf
	$(PYTHON) ./deduce.py test/generic1.pf
	$(PYTHON) ./deduce.py test/generic2.pf
	$(PYTHON) ./deduce.py test/overload1.pf
	$(PYTHON) ./deduce.py test/overload2.pf --error
	$(PYTHON) ./deduce.py test/overload3.pf
	$(PYTHON) ./deduce.py test/overload4.pf --error
	$(PYTHON) ./deduce.py test/overload5.pf
	$(PYTHON) ./deduce.py test/overload6.pf
	$(PYTHON) ./deduce.py test/all1.pf
	$(PYTHON) ./deduce.py test/all2.pf
	$(PYTHON) ./deduce.py test/all3.pf
	$(PYTHON) ./deduce.py test/all4.pf --error
	$(PYTHON) ./deduce.py test/not_equal.pf
	$(PYTHON) ./deduce.py test/bintree.pf
	$(PYTHON) ./deduce.py test/induction1.pf
	$(PYTHON) ./deduce.py test/after.pf
	$(PYTHON) ./deduce.py Base.pf
	$(PYTHON) ./deduce.py Set.pf
	$(PYTHON) ./deduce.py MultiSet.pf
	$(PYTHON) ./deduce.py Maps.pf
	$(PYTHON) ./deduce.py Nat.pf
	$(PYTHON) ./deduce.py NatTests.pf
	$(PYTHON) ./deduce.py Log.pf
	$(PYTHON) ./deduce.py test/some1.pf
	$(PYTHON) ./deduce.py test/some2.pf
	$(PYTHON) ./deduce.py test/inst1.pf
	$(PYTHON) ./deduce.py test/inst2.pf
	$(PYTHON) ./deduce.py test/conditional1.pf
	$(PYTHON) ./deduce.py test/mark1.pf
	$(PYTHON) ./deduce.py test/mark2.pf
	$(PYTHON) ./deduce.py test/mark3.pf
	$(PYTHON) ./deduce.py test/fun1.pf
	$(PYTHON) ./deduce.py List.pf
	$(PYTHON) ./deduce.py ListTests.pf
	$(PYTHON) ./deduce.py Pair.pf
	$(PYTHON) ./deduce.py Binary.pf
	$(PYTHON) ./deduce.py Option.pf

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
