union MyNat.0 {zero.1/0, suc.2/1}
fn used.3($scr0, m.4) = match $scr0 { | zero.1 -> m.4 | suc.2(n.5) -> suc.2(used.3(n.5, m.4)) }
print used.3(suc.2(zero.1), suc.2(suc.2(zero.1)))
