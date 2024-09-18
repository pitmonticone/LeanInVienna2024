import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Functor.Currying

open Real CategoryTheory Limits

-- First: if there is a high-powered tactic that can solve your goal, use it!

example {a b c d : ℕ} (h₁ : a ≤ c) (H₂ : b ≤ d) : a + b ≤ c + d := by
  sorry

example {a b c d : ℕ} (h₁ : a ≤ c) (H₂ : b ≤ d) : a + b + b + b ≤ c + d + d + d := by
  sorry

example : cos 0 = 1 := by
  sorry

example {α : Type} (s t : Set α) : s \ (s ∪ t) = ∅ := by
  sorry

example {α β γ : Type} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β}
    {g : β → γ} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  sorry

example {x : ℝ} : 0 ≤ x ^ 4 := by
  sorry

example {a b c d : ℝ} {hab : a < b} {hbc : c < d} : a + c < b + d := by
  sorry

-- A broad overview over most basic parts of the library is given in the undergrad list:
-- https://leanprover-community.github.io/undergrad.html

-- The mathlib naming convention:
-- https://leanprover-community.github.io/contribute/naming.html

-- When starting to interact with an area of mathlib, it makes sense to explore the relevant files
-- in the mathlib docs for a bit: https://leanprover-community.github.io/mathlib4_docs/index.html

-- Tools for finding things:
-- `excact?`, `apply?`, `hint` tactics for making progress on specific goals
-- Loogle for precise (but possibly broad) searches
-- LeanSearch for natural language search

-- Example 1: Fundamental theorem of algebra

example {p : Polynomial ℂ} (h : 0 < p.degree) : ∃ x, p.eval x = 0 := by
  sorry

-- Example 2: Let's try to find the first isomorphism theorem for modules

-- Example 3: Binary product functor

noncomputable example {C : Type} [Category C] [HasBinaryProducts C] : C × C ⥤ C :=
  sorry

-- Example 4: Square of square root of real number is the original number

example (x : ℝ) : x.sqrt ^ 2 = x := by
  sorry

-- Example 5: Dimension of quotient space is difference of dimensions

example {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) :
    FiniteDimensional.finrank R (M ⧸ N) =
      FiniteDimensional.finrank R M - FiniteDimensional.finrank R N := by
  sorry

-- Example 6: If the number of vectors exceeds the dimension, then the set is linearly dependent

-- Some more LeanSearch examples:

#leansearch "Sandwich theorem"
#leansearch "Sandwich theorem for tendsto"
#leansearch "Binet's formula"
#leansearch "Ratio test for convergence"
#leansearch "Yoneda embedding for preadditive categories"
#leansearch "abelian category has injective cogenerator"

-- If all else fails, ask on Zulip.
