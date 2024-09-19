import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Functor.Currying

open Real CategoryTheory Limits

-- First: if there is a high-powered tactic that can solve your goal, use it!

example {a b c d : ℕ} (h₁ : a ≤ c) (h₂ : b ≤ d) : a + b ≤ c + d := by
  gcongr

theorem foo {a b c d : ℕ} (h₁ : a ≤ c) (h₂ : b ≤ d) : a + b + b + b ≤ c + d + d + d := by
  gcongr

example : cos 0 = 1 := by
  simp

example {α : Type} (s t : Set α) : s \ (s ∪ t) = ∅ := by
  aesop

example {α β γ : Type} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β}
    {g : β → γ} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  fun_prop

example {x : ℝ} : 0 ≤ x ^ 4 := by
  positivity

example {a b c d : ℝ} {hab : a < b} {hbc : c < d} : a + c < b + d := by
  gcongr

-- A broad overview over most basic parts of the library is given in the undergrad list:
-- https://leanprover-community.github.io/undergrad.html

-- The mathlib naming convention:
-- https://leanprover-community.github.io/contribute/naming.html

-- When starting to interact with an area of mathlib, it makes sense to explore the relevant files
-- in the mathlib docs for a bit: https://leanprover-community.github.io/mathlib4_docs/index.html

-- Tools for finding things:
-- `exact?`, `apply?`, `hint` tactics for making progress on specific goals
-- Loogle for precise (but possibly broad) searches
-- LeanSearch for natural language search

-- Example 1: Fundamental theorem of algebra

example {p : Polynomial ℂ} (h : 0 < p.degree) : ∃ x, Polynomial.IsRoot p x := by
  exact Complex.exists_root h -- Found via LeanSearch "fundamental theorme of algebra"

-- Example 2: Let's try to find the first isomorphism theorem for modules

-- Found via LeanSearch or Loogle "LinearMap.ker, LinearMap.range, LinearEquiv"

#check LinearMap.quotKerEquivRange

-- Example 3: Binary product functor

#check prod.functor -- found via Loogle "CategoryTheory.Functor, CategoryTheory.Limits.HasBinaryProducts"
#check uncurry -- found via Loogle 'CategoryTheory.Functor, "curry"'

noncomputable example {C : Type} [Category C] [HasBinaryProducts C] : C × C ⥤ C :=
  uncurry.obj prod.functor

-- Example 4: Square of square root of real number is the original number

-- Found via `apply?`
example (x : ℝ) (hx : 0 ≤ x) : x.sqrt ^ 2 = x := by
  exact sq_sqrt hx

-- Example 5: Dimension of quotient space is difference of dimensions

example {R M : Type} [DivisionRing R] [AddCommGroup M] [Module R M] [FiniteDimensional R M] (N : Submodule R M) :
    FiniteDimensional.finrank R (M ⧸ N) =
      FiniteDimensional.finrank R M - FiniteDimensional.finrank R N := by
  have := Submodule.finrank_quotient_add_finrank N -- Found via Loogle 'FiniteDimensional.finrank, "quot"'
  omega

#leansearch "finrank of quotient space is difference of dimensions"

-- Some more LeanSearch examples:

#leansearch "Sandwich theorem"
#leansearch "Sandwich theorem for tendsto"
#leansearch "Binet's formula"
#leansearch "Ratio test for convergence"
#leansearch "Yoneda embedding for preadditive categories"
#leansearch "abelian category has injective cogenerator"

-- If all else fails, ask on Zulip.
