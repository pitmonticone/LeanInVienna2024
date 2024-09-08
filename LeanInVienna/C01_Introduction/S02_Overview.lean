import LeanInVienna.Common

-- Lean is a formal language for manipulating mathematical objects, propositions and proofs.

-- These are pieces of data.
-- Lean is not a calculator.
#check 2 + 2

-- Lean can be a calculator
#eval 2 + 2
#eval 7^23487

section
variable {R : Type} [CommRing R]
variable (x y z : R)

#conv ring_nf => (x + y + z)^3

end

@[simp]
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 6
#eval List.range 20 |>.map fib

-- These are propositions, of type `Prop`.
#check 2 + 2 = 4
#check 2 + 2 = 5

-- These are proofs of propositions.
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem foo (x y : ℝ) : (x+y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  ring

#print foo

example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say `m` and `n` are natural numbers, and assume `n = 2 * k`.
  rintro m n ⟨k, hk⟩
  -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
  use m * k
  -- Substitute for `n`,
  rw [hk]
  -- and now it's obvious.
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  exact?

theorem bar (x : ℝ) : 2*x ≤ x^2 + 1 := by
  apply le_of_sub_nonneg
  calc
    0 ≤ (x - 1)^2     := by positivity
    _ = x^2 + 1 - 2*x := by ring

#check intermediate_value_univ
open Set

example : ∃ x : ℝ, x^3 + 2*x + 1 = 0 := by
  let f (x : ℝ) := x^3 + 2*x + 1
  suffices 0 ∈ range f by simp_all
  apply intermediate_value_univ (a := -1) (b := 1)
  . fun_prop
  · simp [f]
    norm_num
