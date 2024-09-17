import LeanInVienna.C10_Differential_Calculus.DerivativesCalculationsCommon

noncomputable section

variable (f : ℝ → ℝ) (x₀ : ℝ)

--- derivative of `f` at `x₀`
#check deriv f x₀

example : deriv (fun x : ℝ => x^2) x₀ = 2*x₀ := by simp

-- exercise
example : deriv (fun x : ℝ => x*x) x₀ = 2*x₀ := by sorry


open Real
example : deriv (fun x : ℝ => exp x) x₀ = exp x₀ := by simp
example : deriv (fun x : ℝ => sin x) x₀ = cos x₀ := by simp

-- derivative by hand becase simp does not work
example : deriv (fun x : ℝ => x + x * exp x) x₀ = 1 + (exp x₀ + x₀ * exp x₀) := by 
  rw[deriv_add]
  rw[deriv_id'']
  rw[deriv_mul]
  rw[deriv_id'']
  rw[Real.deriv_exp]
  simp
  apply differentiableAt_id
  apply differentiableAt_exp
  apply differentiableAt_id
  apply DifferentiableAt.mul
  apply differentiableAt_id
  apply differentiableAt_exp

-- exercise - do the calculation using `rw` and `apply`
example : deriv (fun x : ℝ => sin (x + exp x)) x₀ = cos (x₀ + rexp x₀) * (1 + rexp x₀) := by
  sorry

-- use discharger
example : deriv (fun x : ℝ => x + x * exp x) x₀ = 1 + (exp x₀ + x₀ * exp x₀) := by 
  simp (disch:=fun_prop)

example : Differentiable ℝ (fun x : ℝ => x + x * exp x) := by fun_prop
example : Continuous (fun x : ℝ => x + x * exp x) := by fun_prop
example : Measurable (fun x : ℝ => x + x * exp x) := by fun_prop
example : DifferentiableAt ℝ (fun x : ℝ => x + x * exp x) x₀ := by fun_prop
example (h : x₀ ≠ 0) : DifferentiableAt ℝ (fun x : ℝ => 1 / x) x₀ := by fun_prop (disch:=apply h)

-- exercise
example (h : 1 < x₀) : DifferentiableAt ℝ (fun x : ℝ => 1 / (1 - x)) x₀ := by  sorry

-- exercise 
example (h : x₀ ≠ 0) : x₀^2 ≠ 0 := sorry
example (h : x₀ ≠ 0) : DifferentiableAt ℝ (fun x : ℝ => 1 / x^2) x₀ := by sorry


example (h : x₀ ≠ 0) : deriv (fun x : ℝ => sin (1/x)) x₀ = - cos x₀⁻¹ * (x₀ ^ 2)⁻¹ := by 
  simp (disch:=fun_prop (disch:=apply h))


-- use discharger `trace_state; sorry`
example : 
    deriv (fun x : ℝ => sqrt (1 + x^2)) x₀ 
    =
    2 * x₀ / (2 * √(1 + x₀ ^ 2)) := by 
  simp (disch:=first | fun_prop | nlinarith)
  

-- exercise
-- add assumption such that the following holds
example /- add assumption -/ (h : x₀ > -2) : 
    deriv (fun x : ℝ => log (x + 2) * x^3) x₀ 
    =
    (x₀ + 2)⁻¹ * x₀ ^ 3 + log (x₀ + 2) * (3 * x₀ ^ 2)  := by sorry


-- exercise
example (h : x₀ - 1 ≠ 0) (h' : x₀ + 1 ≠ 0) : 
    deriv (fun x : ℝ => sin (1/(x^2 - 1))) x₀ 
    =
    cos (x₀ ^ 2 - 1)⁻¹ * (-(2 * x₀) / (x₀ ^ 2 - 1) ^ 2) := by sorry
  


def S (a b c d : ℝ) : ℝ :=
    a / (a + b + d) + b / (a + b + c) +
    c / (b + c + d) + d / (a + c + d)

def T (t : ℝ) : ℝ := S 1 (1 - t) t (t * (1 - t))


-- exercise
example (h : 0 ≤ x₀) (h' : x₀ ≤ 1) : DifferentiableAt ℝ T x₀ := by
  sorry

-- exercise
example : DifferentiableOn ℝ T (Set.Icc 0 1) := by
  sorry

-- exercise
example  (h : 0 ≤ x₀) (h' : x₀ ≤ 1) : 
    deriv (fun x => T x) x₀ 
    = 
    (x₀ + (x₀ - 1) + 1) / (1 + (1 - x₀) + x₀ * (1 - x₀)) ^ 2 + (-x₀ + (x₀ - 1 + -1)) / (1 + (1 - x₀) + x₀) ^ 2 +
            (1 + x₀ * (1 - x₀) - x₀ * (1 - x₀ + -x₀)) / (1 + x₀ * (1 - x₀)) ^ 2 +
          ((1 - x₀ + -x₀) * (1 + x₀ + x₀ * (1 - x₀)) - x₀ * (1 - x₀) * (1 + (1 - x₀ + -x₀))) / (1 + x₀ + x₀ * (1 - x₀)) ^ 2 := by
  sorry

  

