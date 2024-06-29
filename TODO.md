[ ] implicit instantiation for all's

[ ] change 'let' to 'define'

[x] add let-binding in proofs

[ ] fix generics, implement type passing, see operator ⊆ in Set.pf

[ ] print char_fun(λx{false}) as ∅

[ ] issue of conjunction intro in checking mode

[ ] Revisit syntax for rewriting with a set of equations (replace bar)

[ ] Fix syntax error messages inside imports

[ ] print parenthesis for * and + properly

[ ] create a test feature that adds support for
	[ ] random number generation
	[ ] error (halt with message)
	[ ] loops?

[ ] create student exercises

[ ] specify number of unfoldings in definition and enable

[ ] remove parent param from parser, not needed anymore

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




