union MyNat.5MyNat_0 {zero.5MyNat_1/0, suc.5MyNat_2/1}
fn used.4used_0($scr0, m.4used_1) = match $scr0 { | zero.5MyNat_1 -> m.4used_1 | suc.5MyNat_2(n.4used_2) -> suc.5MyNat_2(used.4used_0(n.4used_2, m.4used_1)) }
print used.4used_0(suc.5MyNat_2(zero.5MyNat_1), suc.5MyNat_2(suc.5MyNat_2(zero.5MyNat_1)))
