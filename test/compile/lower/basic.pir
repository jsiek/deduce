union MyNat.s0_0 {zero.s0_1/0, suc.s0_2/1}
fn add.s1_0($scr0, m.s1_1) = match $scr0 { | zero.s0_1 -> m.s1_1 | suc.s0_2(n.s1_2) -> suc.s0_2(add.s1_0(n.s1_2, m.s1_1)) }
global two.s2_0 = suc.s0_2(suc.s0_2(zero.s0_1))
fn add_two.s3_1(x.s3_0) = add.s1_0(two.s2_0, x.s3_0)
fn pick.s4_3(b.s4_0, x.s4_1, y.s4_2) = if b.s4_0 then x.s4_1 else y.s4_2
print add_two.s3_1(suc.s0_2(zero.s0_1))
print pick.s4_3(true, two.s2_0, zero.s0_1)
