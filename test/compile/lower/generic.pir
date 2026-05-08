union Box.0 {box.2/1}
fn unbox.6(b.4) = match b.4 { | box.2(x.5) -> x.5 }
fn id.10(x.9) = x.9
union MyNat.11 {zero.12/0, suc.13/1}
print id.10(suc.13(zero.12))
print unbox.6(box.2(suc.13(suc.13(zero.12))))
