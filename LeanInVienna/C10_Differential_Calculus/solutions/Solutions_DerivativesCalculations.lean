import LeanInVienna.C10_Differential_Calculus.DerivativesCalculationsCommon

noncomputable section

open Real

variable (x₀ : ℝ)

example : deriv (fun x : ℝ => x*x) x₀ = 2*x₀ := by 
  simp
  ring

example : deriv (fun x : ℝ => sin (x + exp x)) x₀ = cos (x₀ + rexp x₀) * (1 + rexp x₀) := by
  rw[_root_.deriv_sin]
  rw[deriv_add]
  rw[deriv_id'']
  rw[Real.deriv_exp]
  simp
  apply differentiableAt_exp
  apply DifferentiableAt.add
  apply differentiableAt_id 
  apply differentiableAt_exp 


example (h : 1 < x₀) : DifferentiableAt ℝ (fun x : ℝ => 1 / (1 - x)) x₀ := by 
  fun_prop (disch:=linarith)


example (h : x₀ ≠ 0) : x₀^2 ≠ 0 := pow_ne_zero _ h
example (h : x₀ ≠ 0) : DifferentiableAt ℝ (fun x : ℝ => 1 / x^2) x₀ := by 
  fun_prop (disch:=apply pow_ne_zero _ h)

  -- alternative 1
  -- fun_prop (disch:=aesop)

  -- alternative 2
  -- fun_prop (disch:=field_simp)


example (h : x₀ > -2) : 
    deriv (fun x : ℝ => log (x + 2) * x^3) x₀ 
    =
    (x₀ + 2)⁻¹ * x₀ ^ 3 + log (x₀ + 2) * (3 * x₀ ^ 2)  := by 
  simp (disch:=first | fun_prop (disch:=linarith) | linarith)


example (h : x₀ - 1 ≠ 0) (h' : x₀ + 1 ≠ 0) : 
    deriv (fun x : ℝ => sin (1/(x^2 - 1))) x₀ 
    =
    cos (x₀ ^ 2 - 1)⁻¹ * (-(2 * x₀) / (x₀ ^ 2 - 1) ^ 2) := by 

  have h'' : x₀^2 - 1 ≠ 0 := by 
    have hh : x₀^2 - 1 = (x₀ - 1) * (x₀ + 1) := by ring
    rw[hh]; intro hh'
    cases (mul_eq_zero.1 hh') <;> tauto

  simp (disch:=first | fun_prop (disch:=assumption) | assumption)
  


def S (a b c d : ℝ) : ℝ :=
    a / (a + b + d) + b / (a + b + c) +
    c / (b + c + d) + d / (a + c + d)

def T (t : ℝ) : ℝ := S 1 (1 - t) t (t * (1 - t))


example (h : 0 ≤ x₀) (h' : x₀ ≤ 1) : DifferentiableAt ℝ T x₀ := by
  unfold T S
  fun_prop (disch:=nlinarith)

example : DifferentiableOn ℝ T (Set.Icc 0 1) := by
  unfold T S
  fun_prop (disch:=(rintro x ⟨a,b⟩; nlinarith))

example  (h : 0 ≤ x₀) (h' : x₀ ≤ 1) : 
    deriv (fun x => T x) x₀ 
    = 
    (x₀ + (x₀ - 1) + 1) / (1 + (1 - x₀) + x₀ * (1 - x₀)) ^ 2 + (-x₀ + (x₀ - 1 + -1)) / (1 + (1 - x₀) + x₀) ^ 2 +
            (1 + x₀ * (1 - x₀) - x₀ * (1 - x₀ + -x₀)) / (1 + x₀ * (1 - x₀)) ^ 2 +
          ((1 - x₀ + -x₀) * (1 + x₀ + x₀ * (1 - x₀)) - x₀ * (1 - x₀) * (1 + (1 - x₀ + -x₀))) / (1 + x₀ + x₀ * (1 - x₀)) ^ 2 := by
  unfold T S
  simp (disch:=first | fun_prop (disch:=nlinarith) | nlinarith)


  

