import Mathlib


#eval Nat.digits 10 1234

-- without parenthesis, it does not work:
-- #check 10.digits 1234

#eval (10).digits 1234

#eval Nat.digits 1234 10

#eval Nat.ofDigits 10 [4, 3, 2, 1]


-- no check nor casting is done here!
#eval Nat.ofDigits 2 [4, 3, 2, 1]

#eval Nat.ofDigits 7 [(4 : Fin 7), 3, 2, 1]

#eval (7 : ℕ).digits 466

