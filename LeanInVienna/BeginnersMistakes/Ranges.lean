import Mathlib

#check Fin 10

#check List.finRange 10
#eval  List.finRange 10

#check List.range
#eval List.range 10

#check Finset.range 10
#eval Finset.range 10

#eval Finset.Icc 0 10

#check Set.Icc 0 10

theorem finset_eq_set : Set.Icc 0 10 = Finset.Icc 0 10 := Eq.symm (Finset.coe_Icc 0 10)
