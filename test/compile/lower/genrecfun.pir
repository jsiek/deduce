union MyNat.0 {zero.1/0, suc.2/1}
fn iszero.5(n.3) = match n.3 { | zero.1 -> true | suc.2(n'.4) -> false }
fn pred.8(n.6) = match n.6 { | zero.1 -> zero.1 | suc.2(n'.7) -> n'.7 }
fn count_down.22(n.23) = if iszero.5(n.23) then zero.1 else count_down.22(pred.8(n.23))
print count_down.22(suc.2(suc.2(suc.2(zero.1))))
