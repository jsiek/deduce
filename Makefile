
default:
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_true.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_false1.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_false2.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_false3.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_let.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_and.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_and2.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_and3.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_and4.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_implies.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_implies2.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_implies3.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_implies4.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/theorem_or.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/rec1.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/all1.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/all2.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/all3.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/bintree.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/induction1.pf
	/opt/homebrew/bin/python3.10 ./deduce.py Nat.pf
	/opt/homebrew/bin/python3.10 ./deduce.py Log.pf
	/opt/homebrew/bin/python3.10 ./deduce.py Binary.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/some1.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/some2.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/inst1.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/conditional1.pf
	/opt/homebrew/bin/python3.10 ./deduce.py test/fun1.pf
	/opt/homebrew/bin/python3.10 ./deduce.py List.pf
	/opt/homebrew/bin/python3.10 ./deduce.py Pair.pf
#	/opt/homebrew/bin/python3.10 ./deduce.py Heap.pf
	/opt/homebrew/bin/python3.10 ./deduce.py Set.pf
#	/opt/homebrew/bin/python3.10 ./deduce.py Maps.pf
	/opt/homebrew/bin/python3.10 ./deduce.py Option.pf
#	/opt/homebrew/bin/python3.10 ./deduce.py SearchTree.pf
	/opt/homebrew/bin/python3.10 ./deduce.py ex/Sum.pf
	/opt/homebrew/bin/python3.10 ./deduce.py ex/Sort.pf
	/opt/homebrew/bin/python3.10 ./deduce.py ex/MergeSort.pf
	/opt/homebrew/bin/python3.10 ./deduce.py ex/Max.pf
	/opt/homebrew/bin/python3.10 ./deduce.py ex/Search.pf

check_README:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle
	/opt/homebrew/bin/python3.10 ./deduce.py README.pf

check_blog1:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle
	/opt/homebrew/bin/python3.10 ./deduce.py LinkedLists.pf

blog1:
	/usr/local/bin/pandoc Prelude.md -o Prelude.html
	/usr/local/bin/pandoc LinkedLists.md -o LinkedLists.html
	cat Prelude.html LinkedLists.html > blog1.html

check_blog2:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle
	/opt/homebrew/bin/python3.10 ./deduce.py LinearSearch.pf

blog2:
	/usr/local/bin/pandoc LinearSearch.md -o LinearSearch.html

check_blog3:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle
	/opt/homebrew/bin/python3.10 ./deduce.py InsertionSort.pf

blog3:
	/usr/local/bin/pandoc InsertionSort.md -o InsertionSort.html

check_blog4:
	/Users/jsiek/Library/Python/3.11/bin/entangled tangle
	/opt/homebrew/bin/python3.10 ./deduce.py MergeSort.pf

blog4:
	/usr/local/bin/pandoc MergeSort.md -o MergeSort.html


# TODO

