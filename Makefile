BLOG_DIR=/Users/jsiek/deduce-private/blog
EX_DIR=/Users/jsiek/deduce-private/ex
PYTHON=/opt/homebrew/bin/python3.10

default: tests check_docs

check_docs: check_README check_fun check_intro 

tests: #check_blog5
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
	$(PYTHON) ./deduce.py test/fun1.pf
	$(PYTHON) ./deduce.py List.pf
	$(PYTHON) ./deduce.py Pair.pf
	$(PYTHON) ./deduce.py Binary.pf
	$(PYTHON) ./deduce.py Option.pf

examples:
	$(PYTHON) ./deduce.py $(EX_DIR)/Sum.pf
	$(PYTHON) ./deduce.py $(EX_DIR)/Sort.pf
	$(PYTHON) ./deduce.py $(EX_DIR)/MergeSort.pf
	$(PYTHON) ./deduce.py $(EX_DIR)/Max.pf
	$(PYTHON) ./deduce.py $(EX_DIR)/Search.pf
	$(PYTHON) ./deduce.py $(EX_DIR)/Heap2.pf 
#	$(PYTHON) ./deduce.py Heap.pf
#	$(PYTHON) ./deduce.py SearchTree.pf

check_README:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py README.pf

check_fun:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py FunctionalProgramming.pf

check_intro:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py ProofIntro.pf

check_blog1:
	cd $(BLOG_DIR); /Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py $(BLOG_DIR)/LinkedLists.pf

blog1:
	cd $(BLOG_DIR); /usr/local/bin/pandoc Prelude.md -o Prelude.html
	cd $(BLOG_DIR); /usr/local/bin/pandoc LinkedLists.md -o LinkedLists.html
	cd $(BLOG_DIR); cat Prelude.html LinkedLists.html > blog1.html

check_blog2:
	cd $(BLOG_DIR); /Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py $(BLOG_DIR)/LinearSearch.pf

blog2:
	cd $(BLOG_DIR); /usr/local/bin/pandoc LinearSearch.md -o LinearSearch.html

check_blog3:
	cd $(BLOG_DIR); /Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py $(BLOG_DIR)/InsertionSort.pf

blog3:
	cd $(BLOG_DIR); /usr/local/bin/pandoc InsertionSort.md -o InsertionSort.html

check_blog4:
	cd $(BLOG_DIR); /Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py $(BLOG_DIR)/MergeSort.pf

blog4:
	cd $(BLOG_DIR); /usr/local/bin/pandoc MergeSort.md -o MergeSort.html

check_blog5:
	cd $(BLOG_DIR); /Users/jsiek/Library/Python/3.11/bin/entangled tangle 
	$(PYTHON) ./deduce.py $(BLOG_DIR)/BinaryTree.pf
	$(PYTHON) ./deduce.py $(BLOG_DIR)/BinaryTreeTest.pf

blog5:
	cd $(BLOG_DIR); /usr/local/bin/pandoc BinaryTree.md -o BinaryTree.html

check_blog6:
	cd $(BLOG_DIR); /Users/jsiek/Library/Python/3.11/bin/entangled tangle
	$(PYTHON) ./deduce.py $(BLOG_DIR)/BinaryTreeProof.pf

blog6:
	$(BLOG_DIR); /usr/local/bin/pandoc BinaryTreeProof.md -o BinaryTreeProof.html

check_blog7:
	cd $(BLOG_DIR); /Users/jsiek/Library/Python/3.11/bin/entangled tangle
	$(PYTHON) ./deduce.py $(BLOG_DIR)/BinarySearchTree.pf
	$(PYTHON) ./deduce.py $(BLOG_DIR)/BinarySearchTreeTest.pf

blog7:
	cd $(BLOG_DIR); /usr/local/bin/pandoc BinarySearchTree.md -o BinarySearchTree.html

check_blog8:
	cd $(BLOG_DIR); /Users/jsiek/Library/Python/3.11/bin/entangled tangle
	$(PYTHON) ./deduce.py $(BLOG_DIR)/BalancedBST.pf
	$(PYTHON) ./deduce.py $(BLOG_DIR)/BalancedBSTTest.pf

blog8:
	cd $(BLOG_DIR); /usr/local/bin/pandoc BalancedBST.md -o BalancedBST.html

check_blogs:  check_blog1 check_blog2 check_blog3 check_blog4 check_blog5 check_blog6 check_blog7

clean:
	rm -f $(BLOG_DIR)/BinaryTree.pf $(BLOG_DIR)/LinkedLists.pf $(BLOG_DIR)/BinaryTreeProof.pf
	rm -f $(BLOG_DIR)/MergeSort.pf $(BLOG_DIR)/Prelude.pf
	rm -rf $(BLOG_DIR)/InsertionSort.pf $(BLOG_DIR)/LinearSearch.pf
	rm -f $(BLOG_DIR)/BinarySearchTree.pf $(BLOG_DIR)/BinarySearchTreeTest.pf
	rm -f README.pf FunctionalProgramming.pf ProofIntro.pf
	rm -rf .entangled
