union MyNat.0 {zero.1/0, suc.2/1}
union List.3 {empty.5/0, node.6/2}
global A.7 = array(node.6(zero.1, empty.5))
print A.7[suc.2(zero.1)]
