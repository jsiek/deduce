#!/bin/zsh

# requires python cProfile and gprof2dot packages

if [[ -z $1 ]]; then
   echo "Please enter a file to deduce"
else
	python -m cProfile -o profile.pstats deduce.py $1
	python -m gprof2dot -f pstats profile.pstats -o profile.dot
	dot -Tpng -o profile.png profile.dot
	open profile.png

	# clean up
	rm profile.pstats profile.dot
fi
