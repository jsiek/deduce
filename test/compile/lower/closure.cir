union MyNat.23 {zero.24/0, suc.25/1}
fn add.26($scr0, m.27) = match $scr0 { | zero.24 -> m.27 | suc.25(n.28) -> suc.25(add.26(n.28, m.27)) }
fn adder.32(x.30) = closure[$lam1](x.30)
print adder.32(suc.25(zero.24))(suc.25(suc.25(zero.24)))
fn $lam1[x.30](y.31) = add.26(x.30, y.31)
