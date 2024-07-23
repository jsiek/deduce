[ ] add section on rewrite-in to the introduction

[ ] implicit instantiation for all's
  [x] in an apply
  [ ] in checking mode, as part of check_implies?

[ ] print char_fun(λx{false}) as ∅

[ ] issue of conjunction intro in checking mode

[ ] Revisit syntax for rewriting with a set of equations (replace bar)

[ ] Fix syntax error messages inside imports

[ ] create a test feature that adds support for
	[ ] random number generation
	[ ] error (halt with message)
	[ ] loops?

[ ] create student exercises

[ ] specify number of unfoldings in definition and enable

[ ] remove parent param from parser, not needed anymore

[x] fix generics, implement type passing, see operator ⊆ in Set.pf

[x] change how definition works, use substitution insetad of reduce

[x] change 'let' to 'define'

[x] add let-binding in proofs

[x] print parenthesis for * and + properly

[x] don't print globals in available facts

[x] issue of nontermination for foldr in sum_fold

[x] Explain false.

[x] Change order of checking for PAnnot

[x] explain existentials using even number example

[x] Mutually recursive functions

``` {.java file=ex/even_odd.pf}
function is_even(Nat) -> bool {
  is_even(0) = true
  is_even(suc(n)) = is_odd(n)
}

function is_odd(Nat) -> bool {
  is_odd(0) = false
  is_odd(suc(n)) = is_even(n)
}
```




