/-
Copyright (c) 2024 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone
-/
import Mathlib.Tactic

/-!
# Test Lean 4 Environment

This file serves as a basic test to verify that Lean 4 is correctly installed and configured.
By evaluating the expression `2 ^ 5` and checking the correctness of a simple example, you can confirm that:

1. The Lean 4 environment is functioning properly.
2. The `Mathlib` library is correctly imported and available for use.
3. The `#eval` command is working as expected, providing the correct output.
4. Tactics such as `simp` are operating correctly in proofs.
-/

/- Evaluating a simple arithmetic expression to test the Lean environment. -/
#eval 3 ^ 3  -- Expected output: 27

/-- A basic example to verify that the `simp` tactic is functioning correctly. -/
example (x : ℝ) : x - x = 0 := by simp  -- The `simp` tactic simplifies the expression to `0`
