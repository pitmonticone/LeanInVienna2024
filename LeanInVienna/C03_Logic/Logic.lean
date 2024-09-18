import LeanInVienna.Common
import Mathlib.Data.Real.Basic

open Function

/- # Logical Connectives

An overview of the most important logical connectives:

| Symbol     | Code     | Meaning                                   |
|------------|----------|-------------------------------------------|
| `→`        | `\to`  | if ... then ... (implication)             |
| `∀`        | `\all` | for all (universal quantification)        |
| `∃`        | `\ex`  | there exists (existential quantification) |
| `¬`        | `\not` | not (negation)                            |
| `∧`        | `\and` | and (conjunction)                         |
| `∨`        | `\or`  | or (disjunction)                          |
| `↔`        | `\iff` | ... if and only if ... (biimplication)    |
| `False`    |        | contradiction! (falsity)                  |
| `True`     |        | this is trivial (truth)                   |

How to use them in Lean:

| Connective | When appearing as a hypothesis `h`                | When appearing as a target            |
|------------|---------------------------------------------------|--------------------------------------|
| `A → B`    | `have h' := h ha`, `apply h`                      | `intro ha`                           |
| `∀ x, P x` | `have h' := h x`, `apply h`, `specialize`         | `intro x`                            |
| `A ∧ B`    | `rcases h with ⟨ha, hb⟩`, `h.1`, `h.2`            | `constructor`                        |
| `A ∨ B`    | `rcases h with (ha | hb)`                         | `left` or `right`                    |
| `∃ x, P x` | `rcases h with ⟨x, hx⟩`                           | `constructor` or `use x`             |
| `False`    | `contradiction`                                   | --                                   |
| `True`     | --                                                | `trivial`                            |
| `¬ A`      | `contradiction`                                   | `intro ha`                           |
| `A ↔ B`    | `rcases h with ⟨h₁, h₂⟩`                          | `constructor`                        |

-/

namespace Implication

/- # Implications

## Using implications

Lean denotes implication by the symbol `→` instead of `⇒` because it sees a proof
of `P → Q` as a function sending any proof of `P` to a proof of `Q`
(increase font size if you can't see the difference between → and ⇒).

For instance, given a real number `a`, the lemma `sq_pos_of_pos` claims `0 < a → 0 < a^2`
so the proof belows apply the "function" `sq_pos_of_pos` to the assumption `ha`.
-/

example (a : ℝ) (ha : 0 < a) : 0 < a^2 := sq_pos_of_pos ha

/-
The above proof is a direct proof: we already know `0 < a` and we feed this fact into the
implication.
We can also use backward reasoning using the `apply` tactic.
-/

example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a^2`
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a`
  exact ha            -- This is exactly our assumption `ha`.

/-
Try to do the next exercise using the lemma `add_pos : 0 < x → 0 < y → 0 < x + y`.
Note that after you `apply add_pos` you will have two goals, that you will have to
prove one-by-one.
-/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  apply add_pos
  apply sq_pos_of_pos
  exact ha
  apply sq_pos_of_pos
  exact hb

/-
You can also give a proof with forward reasoning, using the `have` tactic.
In order to announce an intermediate statement we use:

  `have my_name : my_statement := by`

This triggers the apparition of a new goal: proving the statement.
After the proof is done, the statement becomes available under the name `my_name`.
If the proof is a single `exact` then you tactic then you can get rid
of `by` and `exact` and directly put the argument of `exact` after the `:=`.
-/

example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  have h2 : 0 < a^2 := by     -- We declare `0 < a^2` as a subgoal
    apply sq_pos_of_pos       -- We start proving the subgoal
    exact ha                  -- This line is indented, so part of the proof of the subgoal
  exact sq_pos_of_pos h2      -- We finished the subgoal, and now we prove the main goal using it.


/- Now prove the same lemma as before using forwards reasoning. -/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  have h2a : 0 < a^2 := by
    exact sq_pos_of_pos ha
  have h2b : 0 < b^2 := sq_pos_of_pos hb -- using the condensed spelling
  exact add_pos h2a h2b


/- ## Proving implications

In order to prove an implication, we need to assume to premise and prove the conclusion.
This is done using the `intro` tactic. Secretly the exercise above was proving the
implication `a > 0 → (a^2)^2 > 0` but the premise was already introduced for us.
-/

example (a b : ℝ) : a > 0 → b > 0 → a + b > 0 := by
  intro ha hb -- You can choose any names here
  exact add_pos ha hb

/- Now prove the following simple statement in propositional logic.
Note that `p → q → r` means `p → (q → r)`. -/
example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by
  intro h1 h2 h3
  apply h2 h3
  exact h1 h3

/- # Equivalences

## Using equivalences to rewrite statements

In the previous file, we saw how to rewrite using equalities.
The analogue operation with mathematical statements is rewriting using
equivalences. This is also done using the `rw` tactic.
Lean uses `↔` to denote equivalence instead of `⇔`
(increase font size if you can't see the difference).

In the following exercises we will use the lemma:

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`
-/

#check sub_nonneg

example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [← sub_nonneg]
  have key : (c + b) - (c + a) = b - a := by-- Here we introduce an intermediate statement named key
    ring   -- and prove it in an indented block (here this block is only one line long)
  rw [key] -- we can now use `key`. This `rw` uses an equality result, not an equivalence
  rw [sub_nonneg] -- and switch back to reach the tautology a ≤ b ↔ a ≤ b

/-
Let's prove a variation
-/

example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by
  rw [← sub_nonneg]
  ring_nf
  rw [sub_nonneg]

/-
The above lemma is already in the mathematical library, under the name `add_le_add_iff_right`:

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

This can be read as: "`add_le_add_iff_right` is a function that will take as input a real
number `c` and will output a proof of `a + c ≤ b + c ↔ a ≤ b`". Here is an example where this lemma
is used.
-/

example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by rw [add_le_add_iff_right b] ; exact ha

/-
## Using equivalences as pairs of implications

In the second line in the above proof is a bit silly: we use statement rewriting to reduce
the goal to our assumption `ha`, but it would be more natural to see the equivalence as a
double implication. We can access the two implications of an equivalence `h : P ↔ Q` as
`h.1 : P → Q` and `h.2 : Q → P`. This allows to rewrite the above proof as:
-/

example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha

/- Let's do a variant using `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` instead. -/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  calc
    a = a + 0 := by ring
    _ ≤ a + b := by exact (add_le_add_iff_left a).2 hb

/-
## Proving equivalences

In order to prove an equivalence one can use `rw` until the
goal is the tautology `P ↔ P`, just as one can do with equalities.

One can also separately prove the two implications using the `constructor` tactic.

Here is an example.
-/

example (a b : ℝ) : (a-b)*(a+b) = 0 ↔ a^2 = b^2 := by
  constructor
  · intro h
    calc
      a ^ 2 = b^2 + (a - b) * (a + b)  := by ring
          _ = b^2 + 0                  := by rw [h]
          _ = b^2                      := by ring
  · intro h
    calc
      (a-b)*(a+b) = a^2 - b^2  := by ring
                _ = b^2 - b^2  := by rw [h]
                _ = 0          := by ring


/- You can try it yourself in this exercise. -/

example (a b : ℝ) : a = b ↔ b - a = 0 := by
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    calc
      a = b - (b - a) := by ring
      _ = b - 0       := by rw [h]
      _ = b           := by ring

end Implication

namespace Negation

/-
# Negation statements

Next we'll look at `False` and negation statements. `False` is defined to
be a `Prop` with no terms. Meanwhile, negation statements are statements
beginning with `¬`, which you can type with `\not`. Given a proposition `P`,
`¬ P` is defined to mean `P → False`, so it's an implication statement in disguise.
-/
example (P : Prop) : P → ¬¬ P := by
  intro hP
  intro hnotP
  apply hnotP
  exact hP

example (P : Prop) : P → ¬¬ P := by
  intro hP
  intro hnotP
  apply hnotP
  exact hP

/- To derive another proposition from a proof of `False`, we use the `exfalso` tactic: -/
example (P : Prop) : False → P := by
  intro hFalse
  exfalso
  exact hFalse

/- Finally, note that `x ≠ y` is notation for `¬(x = y)`. -/
example (a b : ℕ) : a ≠ b → b ≠ a := by
  intro hab hnot
  apply hab
  rw [hnot]

end Negation

namespace UniversalQuantifier

/- # Universal quantifiers

In this file, we'll learn about the `∀` quantifier.

Let `P` be a predicate on a type `X`. This means for every mathematical
object `x` with type `X`, we get a mathematical statement `P x`.
In Lean, `P x` has type `Prop`.

Lean sees a proof `h` of `∀ x, P x` as a function sending any `x : X` to
a proof `h x` of `P x`.
This already explains the main way to use an assumption or lemma which
starts with a `∀`.

In order to prove `∀ x, P x`, we use `intro x` to fix an arbitrary object
with type `X`, and call it `x` (`intro` stands for "introduce").

Note also we don't need to give the type of `x` in the expression `∀ x, P x`
as long as the type of `P` is clear to Lean, which can then infer the type of `x`.

Let's define a predicate to play with `∀`.
-/

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
In the next proof, we also take the opportunity to introduce the
`unfold` tactic, which simply unfolds definitions. Here this is purely
for didactic reason, Lean doesn't need those `unfold` invocations.
We will also use the `rfl` tactic, which proves equalities that are true
by definition (in a very strong sense), it stands for "reflexivity".
-/

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- Our assumption on that f is even means ∀ x, f (-x) = f x
  unfold even_fun at hf
  -- and the same for g
  unfold even_fun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- Let x be any real number
  intro x
  -- and let's compute
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl


/-
Tactics like `unfold`, `apply`, `exact`, `rfl` and `calc` will automatically unfold definitions.
You can test this by deleting the `unfold` lines in the above example.

Tactics like `rw`, `ring` and `linarith` will generally
not unfold definitions that appear in the goal.
This is why the first computation line is necessary, although its proof is simply `rfl`.
Before that line, `rw hf x` won't find anything like `f (-x)` hence will give up.
The last line is not necessary however, since it only proves
something that is true by definition, and is not followed by a `rw`.

Also, Lean doesn't need to be told that `hf` should be specialized to
`x` before rewriting, exactly as in the first file.

Recall also that `rw` can take a list of expressions to use for
rewriting. For instance `rw [h₁, h₂, h₃]` is equivalent to three
lines `rw [h₁]`, `rw [h₂]` and `rw [h₃]`. Note that you can inspect the tactic
state between those rewrites when reading a proof using this syntax. You
simply need to move the cursor inside the list.

Hence we can compress the above proof to:
-/

example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]

/-
Now let's practice. Recall that if you need to learn how to type a unicode
symbol you can put your mouse cursor above the symbol and wait for one second.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by
  intro x
  calc
    (g ∘ f) (-x) = g (f (-x))   := by rfl
               _ = g (f x)      := by rw [hf]

/-
Let's have more quantifiers, and play with forward and backward reasoning.

In the next definitions, note how `∀ x₁, ∀ x₂, ...` is abbreviated to `∀ x₁ x₂, ...`.
-/

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

/- Let's be very explicit and use forward reasoning first. -/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- Since f is non-decreasing, f x₁ ≤ f x₂.
  have step₁ : f x₁ ≤ f x₂ := hf x₁ x₂ h
  -- Since g is non-decreasing, we then get g (f x₁) ≤ g (f x₂).
  exact hg (f x₁) (f x₂) step₁

/-
In the above proof, note how inconvenient it is to specify `x₁` and `x₂` in `hf x₁ x₂ h` since
they could be inferred from the type of `hf`.
We could have written `hf _ _ h` and Lean would have filled the holes denoted by `_`.
The same remark applies to the last line.

One possible variation on the above proof is to
use the `specialize` tactic to replace `hf` by its specialization to the relevant value.
 -/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  specialize hf x₁
  specialize hf x₂
  specialize hf h
  exact hg (f x₁) (f x₂) hf

/-
This `specialize` tactic is mostly useful for exploration, or in preparation for rewriting
in the assumption. One can very often replace its use by using more complicated expressions
directly involving the original assumption, as in the next variation:
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)

/-
Let's see how backward reasoning would look like here.
As usual with this style, we use `apply` and enjoy Lean specializing assumptions for us
using so-called unification.
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- We need to prove (g ∘ f) x₁ ≤ (g ∘ f) x₂.
  -- Since g is non-decreasing, it suffices to prove f x₁ ≤ f x₂
  apply hg
  -- which follows from our assumption on f
  apply hf
  -- and on x₁ and x₂
  exact h

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by
  intro x₁ x₂ h
  apply hg
  exact hf x₁ x₂ h

/- More exmaples -/

example : ∀ P : Prop, False → P := by
  intro P hFalse
  exfalso
  exact hFalse

section
variable {α β γ : Type}

def Injective (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y

example (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  unfold Injective at hf hg ⊢
  intro X Y hXY
  apply hf
  apply hg
  exact hXY

/- If you want to see what's going on better, you can use the `specialize`
tactic to partially apply a local hypothesis to some inputs. -/
example (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  intro X Y hXY
  unfold Injective at hf
  specialize hf X Y
  apply hf
  specialize hg (f X) (f Y)
  apply hg
  exact hXY
end

/- # Finding lemmas

Lean's mathematical library contains many useful facts,
and remembering all of them my name is infeasible.
The following exercises teach you two such techniques.
* `simp` will simplify complicated expressions.
* `apply?` will find lemmas from the library.
-/

/- Use `simp` to prove the following. Note that `X : Set ℝ`
means that `X` is a set containing (only) real numbers. -/
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by
  simp
  exact hx

/- Use `apply?` to find the lemma that every continuous function with compact support
has a global minimum. -/

example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by
  -- use `apply?` to find:
  exact Continuous.exists_forall_le_of_hasCompactSupport hf h2f

end UniversalQuantifier


namespace Conjunction

/-
## Conjunctions

In this file, we learn how to handle the conjunction ("logical and") operator
and the existential quantifier.

In Lean the conjunction of two statements `P` and `Q` is denoted by `P ∧ Q`, read as "P and Q".

We can use a conjunction similarly to the `↔`:
* If `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`.
* To prove `P ∧ Q` use the `constructor` tactic.

Furthermore, we can decompose conjunction and equivalences.
* If `h : P ∧ Q`, the tactic `rcases h with ⟨hP, hQ⟩`
  gives two new assumptions `hP : P` and `hQ : Q`.
* If `h : P ↔ Q`, the tactic `rcases h with ⟨hPQ, hQP⟩`
  gives two new assumptions `hPQ : P → Q` and `hQP : Q → P`.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq

/- One can also prove a conjunction without the constructor tactic by gathering both sides
using the `⟨`/`⟩` brackets, so the above proof can be rewritten as. -/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩

/- You can choose your own style in the next exercise. -/

example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  constructor
  · intro h h'
    rcases h' with ⟨hp, hq⟩
    exact h hp hq
  · intro h hp hq
    apply h
    constructor
    · exact hp
    · exact hq


/- Of course Lean doesn't need any help to prove this kind of logical tautologies.
This is the job of the `tauto` tactic, which can prove true statements in propositional logic. -/
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  tauto

end Conjunction

namespace ExistentialQuantifier

/- # Extential quantifiers

In order to prove `∃ x, P x`, we give some `x₀` using tactic `use x₀` and
then prove `P x₀`. This `x₀` can be an object from the local context
or a more complicated expression. In the example below, the property
to check after `use` is true by definition so the proof is over.
-/
example : ∃ n : ℕ, 8 = 2*n := by
  use 4

/-
In order to use `h : ∃ x, P x`, we use the `rcases` tactic to fix
one `x₀` that works.

Again `h` can come straight from the local context or can be a more
complicated expression.
-/
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by
  -- Let's fix k₀ such that n = k₀ + 1.
  rcases h with ⟨k₀, hk₀⟩
  -- It now suffices to prove k₀ + 1 > 0.
  rw [hk₀]
  -- and we have a lemma about this
  exact Nat.succ_pos k₀


/- We can use an `∃` statement by deconstructing it and replacing
`∃ x, P x` with a term `x : α` and a hypothesis `hx : P x`. -/
example (α : Type) (P : α → Prop) (h : ∃ x, P x) : ¬ (∀ x, ¬ P x) := by
  intro hnot
  rcases h with ⟨x, hx⟩
  apply hnot
  exact hx

example (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) :
    ∃ x, Q x ∧ P x := by
  rcases h with ⟨x, hPx, hQx⟩
  use x, hQx, hPx

example (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) :
    ∃ x, Q x ∧ P x := by
  rcases h with ⟨x, hPx, hQx⟩
  constructor
  · use hQx, hPx

example (α : Type) (P Q : α → Prop) :
    (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  rintro ⟨x, hPx, hQx⟩
  use x, hQx, hPx

/-
We can now start combining quantifiers, using the definition

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`
-/

example (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by
  intro y
  rcases h y with ⟨w, hw⟩
  use f w
  exact hw

end ExistentialQuantifier

namespace ClassicalLogic

/- ## Classical logic -/

variable (P Q : Prop) (α : Type)

/- To prove this we need to use classical logic, and apply the law of excluded middle: -/
lemma not_not : ¬¬P → P := by
  by_cases hP : P -- we case-split on `P ∨ ¬P`
  · intro h
    assumption
  · intro h
    exfalso
    exact h hP

/- The tactic `by_contra` just applies `not_not`: -/
example : ¬¬P → P := by
  intro hP
  by_contra hP'
  exact hP hP'

/- You can use `not_not` to prove the following lemma directly.
Alternatively, there are various tactics which use classical logic
and are useful here: -/
example : ¬(P → Q) → P ∧ ¬Q := by
  tauto
/- `tauto` can prove pretty much everything in this file so far. -/

/- `push_neg` simplifies negation statements by "pushing" the
negation as far inside the statement as possible: -/
example : ¬(P → Q) → P ∧ ¬Q := by
  push_neg
  intro hP
  assumption

/- We can also `push_neg` at a hypothesis: -/
example (P : α → Prop) (h : ¬∀ x, ¬P x) : ∃ x, P x := by
  push_neg at h
  assumption

/- And `push_neg` can also simplify inequalities: -/
example : ¬(∃ n : ℕ, ¬(3 < n) ∧ ¬(n ≤ 5)) := by
  push_neg
  intro n
  tauto

/- `contrapose` replaces a `p → q` goal with the contrapositive,
`¬q → ¬p`. `contrapose!` combines this with `push_neg`. -/
example : ¬(P → Q) → P ∧ ¬Q := by
  contrapose
  push_neg
  intro hPQ
  assumption

end ClassicalLogic

section Exercises

/-!
## Additional Exercises
-/

variable (p q : Prop)
variable (r s : ℕ → Prop)

example : p ∧ q → q ∧ p := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  exact ⟨hq, hp⟩

example : p ∨ q → q ∨ p := by
  intro hpq
  rcases hpq with (hp|hq)
  · right
    assumption
  · left
    assumption

example : (∃ x, r x ∧ s x) → (∃ x, r x) ∧ (∃ x, s x) := by
  intro h
  rcases h with ⟨x, hrx, hsx⟩
  constructor
  · use x
  · use x

example : ∀ z, (∃ x y, r x ∧ s y ∧ y = z) → ∃ x, r x ∧ s z := by
  intro z h
  rcases h with ⟨x, y, hr, hx, rfl⟩
  use x

example : ¬¬(¬¬p → p) := by
  intro h
  apply h
  intro hnnp
  exfalso
  apply hnnp
  intro hp
  apply h
  intro
  assumption

example : ∃ x, r x → ∀ y, r y := by
  by_cases h : ∀ y, r y
  · use 0
    intro _
    assumption
  · push_neg at h
    rcases h with ⟨w, hw⟩
    use w
    intro hw'
    contradiction

end Exercises
