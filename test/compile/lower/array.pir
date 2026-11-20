union MyNat.5MyNat_0 {zero.5MyNat_1/0, suc.5MyNat_2/1}
union List.4List_0 {empty.4List_2/0, node.4List_3/2}
global ns.2ns_0 = node.4List_3(zero.5MyNat_1, node.4List_3(suc.5MyNat_2(zero.5MyNat_1), node.4List_3(suc.5MyNat_2(suc.5MyNat_2(zero.5MyNat_1)), empty.4List_2)))
global A.1A_0 = array(ns.2ns_0)
print A.1A_0
print A.1A_0[zero.5MyNat_1]
print A.1A_0[suc.5MyNat_2(zero.5MyNat_1)]
print A.1A_0[suc.5MyNat_2(suc.5MyNat_2(zero.5MyNat_1))]
