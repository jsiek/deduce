union MyNat.76 {zero.77/0, suc.78/1}
fn used.79($scr0, m.80) = match $scr0 { | zero.77 -> m.80 | suc.78(n.81) -> suc.78(used.79(n.81, m.80)) }
print used.79(suc.78(zero.77), suc.78(suc.78(zero.77)))
