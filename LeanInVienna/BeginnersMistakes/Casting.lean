import Mathlib

#check 7
#check (7 : ℕ)

#check 7 / 3

#eval 7 / 3

#check (7 : ℚ) / 3
#eval (7 : ℚ) / 3

#check (42 : Fin 10)
#eval (42 : Fin 10)

#check 3 - 7
#eval 3 - 7

#eval (3 : ℤ) - 7


#eval Nat.gcd 12 16

theorem true_gcd : Nat.gcd (12 - 12) (16 - 12) = 4 := by decide

theorem false_gcd : Nat.gcd (12 - 16) (16 - 16) ≠ 4 := by decide

theorem true_gcd_int : Int.gcd (12 - 16) (16 - 16) = 4 := by decide

#check Nat.sqrt 17
#eval Nat.sqrt 17

theorem sqrt_pow_two (n : ℕ) : n.sqrt ^ 2 = n ↔ IsSquare n := by
  constructor
  · intro h
    use n.sqrt
    rw [← Nat.pow_two]
    symm
    exact h
  · intro h
    obtain ⟨z, hz⟩ := h
    rw [hz, Nat.sqrt_eq]
    exact Nat.pow_two z

example (x : ℕ) : x / (1 - 3 / 2) = 0 := by simp

example (x : ℚ) : x / (1 - 3 / 2) = - 2 * x := by
  field_simp
  ring

example (x : ℝ) (hx : x.sqrt = x ^ (1 / 2)) : x = 1 := by
  exact Real.sqrt_eq_one.mp hx

open BigOperators

theorem false_zero_sum : ∑' k : ℕ, k / 2 ^ k ≠ 2 := by
  have : ∑' k : ℕ, k / 2 ^ k = ∑' k : ℕ, 0  := by
    congr
    ext n
    by_cases hn : n = 0
    · rw [hn]
      rfl
    · have : n < 2 ^ n := by exact Nat.lt_two_pow n
      exact Nat.div_eq_of_lt this
  rw [this]
  norm_num
