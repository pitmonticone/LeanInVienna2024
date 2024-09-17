import Mathlib

--- Few theorems that are missing from mathlib to make everything work

@[simp]
theorem deriv_const_sub' (c x : ℝ) : deriv (HSub.hSub c) x = -1 := by
  conv in (HSub.hSub _) => eta_expand
  rw[deriv_const_sub (f:=fun x => x)]
  simp

@[simp]
theorem deriv_const_add'' (c x : ℝ) : deriv (HAdd.hAdd c) x = 1 := by
  conv in (HAdd.hAdd _) => eta_expand
  rw[deriv_const_add (f:=fun x => x)]
  simp

@[simp]
theorem deriv_const_mul' (c x : ℝ) : deriv (HMul.hMul c) x = c := by
  conv in (HMul.hMul _) => eta_expand
  rw[deriv_const_mul (d:=fun x => x)]
  simp (disch:=fun_prop); fun_prop

open Real in
attribute [fun_prop] 
  differentiable_sin differentiableAt_sin
  differentiable_cos differentiableAt_cos
  Differentiable.sqrt DifferentiableAt.sqrt
