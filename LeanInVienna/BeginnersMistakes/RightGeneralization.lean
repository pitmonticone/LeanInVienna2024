import Mathlib


-- try searching for it!
theorem odd_iff_square_odd (m : ℕ) : Odd m ↔ Odd (m ^ 2) := by
  -- exact?
  sorry

theorem odd_iff_power_odd (n m : ℕ) (h : n ≠ 0) : Odd m ↔ Odd (m ^ n) := by
  rw [← not_iff_not]
  simp only [← Nat.not_even_iff_odd, not_not]
  exact Iff.symm (Nat.even_pow' h)
