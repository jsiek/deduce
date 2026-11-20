union MyNat.5MyNat_0 {zero.5MyNat_1/0, suc.5MyNat_2/1}
fn add.3add_0($scr0, m.3add_1) = match $scr0 { | zero.5MyNat_1 -> m.3add_1 | suc.5MyNat_2(n.3add_2) -> suc.5MyNat_2(add.3add_0(n.3add_2, m.3add_1)) }
global two.3two_0 = suc.5MyNat_2(suc.5MyNat_2(zero.5MyNat_1))
fn add_two.7add_two_1(x.7add_two_0) = add.3add_0(two.3two_0, x.7add_two_0)
fn pick.4pick_3(b.4pick_0, x.4pick_1, y.4pick_2) = if b.4pick_0 then x.4pick_1 else y.4pick_2
print add_two.7add_two_1(suc.5MyNat_2(zero.5MyNat_1))
print pick.4pick_3(true, two.3two_0, zero.5MyNat_1)
