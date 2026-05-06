union MyNat.9 {zero.10/0, suc.11/1}
fn add.12($scr0, m.13) = match $scr0 { | zero.10 -> m.13 | suc.11(n.14) -> suc.11(add.12(n.14, m.13)) }
global two.16 = suc.11(suc.11(zero.10))
fn add_two.18(x.17) = add.12(two.16, x.17)
fn pick.22(b.19, x.20, y.21) = if b.19 then x.20 else y.21
print add_two.18(suc.11(zero.10))
print pick.22(true, two.16, zero.10)
