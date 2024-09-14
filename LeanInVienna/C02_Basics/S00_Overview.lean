import LeanInVienna.Common

open Nat

/-
# Overview

Lean is an open-source, general-purpose, extensible, dependently-typed functional programming
language and interactive proof assistant based on a version of dependent type theory
known as the *Calculus of Inductive Constructions*.

Every expression has a *type*, and you can use the `#check` command to
print it. Some expressions have types like `ℕ` or `ℕ → ℕ`.

These are mathematical objects.
-/

-- These are pieces of data.
#check 2 + 2

def f (x : ℕ) := x + 3

#check f

/- We can express propositions, which are terms of type `Prop`. -/

#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem

/-
Some expressions are terms of type `P` where `P` itself is a term of type `Prop`.
Such an expression is a proof of the proposition `P`.
-/

theorem easy : 2 + 2 = 4 := rfl

#check easy

theorem hard : FermatLastTheorem := sorry

#check hard

/-
Given that we are trying to build complex expressions, Lean offers two ways of going about it:
- *term mode*: we can write down the expressions themselves;
- *tactic mode*: we can invoke metaprograms called *tactics* which provide instructions to
construct the expressions.

For example, the following expression represents a proof of the fact that
if `n` is even then so is `m * n`:
-/
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

/- The *proof term* can be compressed to a single line: -/
example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

/- The following is, instead, a *tactic-style* proof of the same theorem, where lines
starting with `--` are comments, hence ignored by Lean: -/
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Introduce `m` and `n` and decompose the hypothesis `Even n` to a `k` and the assumption that `n = 2 * k`
  rintro m n ⟨k, hk⟩
  -- Declare we are going to show that `m * n` is even by showing `m * n = 2 * (m * k)`.
  use m * k
  -- Replace `n` by `2 * k` in the target.
  rw [hk]
  -- Resolve by using ring properties.
  ring

/-
The ability to build a proof in small steps with incremental feedback is extremely powerful.
For that reason, tactic proofs are often easier and quicker to write than proof terms.

In our example, the tactic proof can also be reduced to a one-liner:
-/
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

/-
Here we have used tactics to carry out small proof steps. But they can also provide substantial
automation, and justify longer calculations and bigger inferential steps.

For example, we can invoke Lean's simplifier with specific rules for simplifying statements about
parity to prove our theorem automatically.
-/
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
