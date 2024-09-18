import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import LeanInVienna.Common

open Set

-- The type of subsets of `ℕ`
#check Set ℕ

-- Set builder notation
def evens : Set ℕ := { a | a % 2 = 0 }
def odds : Set ℕ := { a | a % 2 = 1 }

#check (∅ : Set ℕ)
#check (univ : Set ℕ)

theorem evens_union_odds : evens ∪ odds = univ := by
  -- Prove set equality using `ext`.
  -- `ext` tactic: if two things are made of the same things, then they are equal.
  -- Works for sets, functions, ... (user-extensible)
  ext n
  -- `simp` tactic: simplify the expression using pre-defined and user-supplied rules
  simp [evens, odds]
  -- `omega` tactic: solve obvious goals about naturals and integers
  omega

def f (x : ℕ) : ℕ :=
  2 * x + 1

theorem f_evens_subset_odds : f '' evens ⊆ odds := by
  -- Prove `⊆` with `intro`.
  rw [subset_def] -- This is optional
  intro n hn
  simp [evens] at hn
  -- `rcases` tactic: destruct hypotheses
  rcases hn with ⟨x, hx, rfl⟩
  simp [f, odds]
  omega

theorem preimage_f_evens : f ⁻¹' evens = ∅ := by
  -- Prove set equality using `ext`.
  ext x
  simp [f, evens]
  omega

-- Bounded quantifiers: `∀ x ∈ s, P x` is the same as `∀ x, x ∈ s → P x`
theorem mod_four_eq_one_of_mem_f_evens : ∀ n ∈ f '' evens, n % 4 = 1 := by
  rintro - ⟨n, hn, rfl⟩
  simp_all [evens, f]
  omega

-- The type of `ℕ`-indexed families of subsets of `ℕ`.
#check ℕ → Set ℕ

-- A specific `ℕ`-indexed family of subsets of `ℕ`.
def residueClassModFive : ℕ → Set ℕ :=
  fun residue => { x | x % 5 = residue }

theorem residueClassModFive_empty (residue : ℕ) (h : 5 ≤ residue) :
    residueClassModFive residue = ∅ := by
  ext x
  simp [residueClassModFive]
  omega

theorem iUnion_residueClassModFive : ⋃ i, residueClassModFive i = univ := by
  ext x
  simp [residueClassModFive]

section
variable {α I : Type} (s : Set α) (A : I → Set α)

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

end

#check Classical.choose
#check Classical.choose_spec

/-
# Operations on sets

| Symbol     | Code            | Meaning                                       |
|------------|-----------------|-----------------------------------------------|
| `∈`        | `\in`           | Set membership                                |
| `∉`        | `\notin`        | Set non-membership                            |
| `⊆`        | `\subset`       | Subset (`s ⊆ t` defined as `x ∈ s → x ∈ t`)   |
| `∪`        | `\union`        | Union of sets                                 |
| `∩`        | `\inter`        | Intersection of sets                          |
| `⋃`        | `\Union`        | Union of indexed family sets                  |
| `⋂`        | `\Inter`        | Intersection of indexed family sets           |
| `\`        | `\setminus`     | Difference of sets                            |
| `∅`       | `\empty`        | The empty set                                 |
| `univ`     |                 | The universal set                             |
| `''`       |                 | Image of set under function                   |
| `⁻¹'`      | `\inv`  `'`     | Preimage of set under function                |
-/

#print Function.Surjective
#print Function.Injective
#print InjOn
