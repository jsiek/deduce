union MyNat.0 {zero.1/0, suc.2/1}
fn add.3($scr0, m.4) = match $scr0 { | zero.1 -> m.4 | suc.2(n.5) -> suc.2(add.3(n.5, m.4)) }
fn adder.9(x.7) = closure[$lam1](x.7)
print adder.9(suc.2(zero.1))(suc.2(suc.2(zero.1)))
fn $lam1[x.7](y.8) = add.3(x.7, y.8)
