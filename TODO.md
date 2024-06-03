[x] explain existentials using even number example

[x] Mutually recursive functions

		function is_even(Nat) -> bool {
		  is_even(0) = true
		  is_even(suc(n)) = is_odd(n)
		}

		function is_odd(Nat) -> bool {
		  is_odd(0) = false
		  is_odd(suc(n)) = is_even(n)
		}

[ ] Revisit syntax for rewriting with a set of equations (replace bar)

[ ] Fix syntax error messages inside imports

[ ] print parenthesis for * and + properly

[ ] Fix bug in multiple rewrites, see theorem addition_of_evens in Nat.pf.

