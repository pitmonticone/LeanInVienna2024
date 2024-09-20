import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Nat.Fib.Basic

open Lean Meta Elab Tactic

-- Extend an existing tactic via attribute

def f (x : ℕ) : ℕ := if x = 0 then 0 else 1

theorem f_zero : f 0 = 0 := by
  simp [f]

example : f 0 + f 1 = f 1 := by
  sorry

@[simp]
theorem Nat.add_one_add_one {n : ℕ} : n + 1 + 1 = n + 2 :=
  rfl

-- Add new notation

def g (x y : ℕ) : ℕ := x + y

notation a " !! " b => g a b

#check 5 !! 8
#check g 5 8
#eval 5 !! 8

section
variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

#check M →ₗ[R] M

end

#check integral_sin

#eval (fun x : Nat ↦ x + 2) 2
#eval (x : Nat ↦ x + 2) 2 -- 4

macro x:ident ":" t:term " ↦ " y:term : term =>
  `(fun $x : $t => $y)

#eval (x : Nat ↦ x + 2) 2 -- 4

macro x:ident " ↦ " y:term : term =>
  `(fun $x  => $y)

#eval (x ↦ x + 2) 2 -- 4

-- Create new tactics using macros

macro "fibonacci_induction" : tactic => `(tactic|(
  intro n
  induction n
  · simp
  · simp_all [Finset.range_succ, Nat.add_assoc, Nat.fib_add_two]
    try ring))

example : ∀ {n : ℕ}, ∑ k in Finset.range n, Nat.fib k + 1 = Nat.fib (n + 1) := by
  fibonacci_induction

example : ∀ {n : ℕ}, ∑ k in Finset.range (n + 1), (Nat.fib k)^2 = Nat.fib n * Nat.fib (n + 1) := by
  fibonacci_induction

-- Create new tactics via elaborators

def myAssumption (mvarId : MVarId) : MetaM (List MVarId) := do
  -- Check that `mvarId` is not already assigned.
  mvarId.checkNotAssigned `myAssumption
  -- Use the local context of `mvarId`.
  mvarId.withContext do
    -- The target is the type of `mvarId`.
    let target ← mvarId.getType
    -- For each hypothesis in the local context:
    for ldecl in ← getLCtx do
      -- If the hypothesis is an implementation detail, skip it.
      if ldecl.isImplementationDetail then
        continue
      -- If the type of the hypothesis is definitionally equal to the target
      -- type:
      if ← isDefEq ldecl.type target then
        -- Use the local hypothesis to prove the goal.
        mvarId.assign ldecl.toExpr
        -- Stop and return an empty list of new goals
        return []
    -- If we have not found any suitable local hypothesis, fail.
    failure

elab "myAssumption" : tactic => liftMetaTactic myAssumption

example {x y : ℕ} (h : x = y) (_h : x = y + y) : x = y := by
  myAssumption

-- Write a linter

#check Mathlib.Linter.refineLinter

-- Attribute magic

@[to_additive]
theorem my_mul_one {G : Type} [Group G] {g : G} : g * 1 = g :=
  MulOneClass.mul_one g

#check my_add_zero

-- Add a command
elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM
    try
      let tp ← elabType typeStx
      discard $ elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch | _ => throwError "failure"

#assertType 5  : Nat

#assertType [] : Nat

#min_imports

-- Create a widget

-- SciLean: https://github.com/lecopivo/SciLean
-- String diagram widget: https://github.com/leanprover-community/mathlib4/blob/master/test/StringDiagram.lean

-- Embed a DSL

-- Lake DSL: https://github.com/leanprover-community/mathlib4/blob/master/lakefile.lean
-- SSFT24: https://github.com/david-christiansen/ssft24/blob/main/Imp.lean
-- Chess: https://github.com/dwrensha/animate-lean-proofs/blob/main/Chess.lean
