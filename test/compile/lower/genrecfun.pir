union MyNat.5MyNat_0 {zero.5MyNat_1/0, suc.5MyNat_2/1}
fn iszero.6iszero_2(n.6iszero_0) = match n.6iszero_0 { | zero.5MyNat_1 -> true | suc.5MyNat_2(n'.6iszero_1) -> false }
fn pred.4pred_2(n.4pred_0) = match n.4pred_0 { | zero.5MyNat_1 -> zero.5MyNat_1 | suc.5MyNat_2(n'.4pred_1) -> n'.4pred_1 }
fn count_down.10count_down_0(n.10count_down_1) = if iszero.6iszero_2(n.10count_down_1) then zero.5MyNat_1 else count_down.10count_down_0(pred.4pred_2(n.10count_down_1))
print count_down.10count_down_0(suc.5MyNat_2(suc.5MyNat_2(suc.5MyNat_2(zero.5MyNat_1))))
