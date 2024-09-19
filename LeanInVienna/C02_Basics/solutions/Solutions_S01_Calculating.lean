import LeanInVienna.Common
import Mathlib.Data.Real.Basic

/- The following exercises with `calc` blocks from *The Mechanics of Proof* by Heather Macbeth.
 The solutions are provided by Pietro Monticone. -/

example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring

example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * 3 := by rw [h2, h1]
    _ = -7 := by ring

example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
    _ = 2 := by ring

example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) = d * a * f - d * b * e := by ring
    _ = b * c * f - b * d * e := by rw [mul_comm d a, h1, mul_comm d b]
    _ = b * (c * f) - b * (d * e) := by repeat rw [mul_assoc]
    _ = 0 := by rw [h2]; ring


example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring

example {x : ℤ} (h1 : x + 4 = 2) : x = - 2 :=
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = - 2 := by ring

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = 4 + 5 * (b + 2) - 5 * 2 := by ring
    _ = 4 + 5 * 3 - 5 * 2 := by rw [h2]
    _ = 9 := by ring

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = (3 * w + 1) / 3 - 1 / 3 := by ring
    _ = 4 / 3 - 1 / 3 := by rw [h1]
    _ = 1 := by ring

example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
    x = (2 * x + 3) - x - 3  := by ring
    _ = x - x - 3 := by rw [h1]
    _ = -3 := by ring

example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x = (2 * x - y) + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring

example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = ((u + 2 * v) + (u - 2 * v)) / 2 := by ring
    _ = (4 + 6) / 2 := by rw [h1, h2]
    _ = 5 := by ring

example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x = (3 * (x + y) + (5 * x - 3 * y)) / 8 := by ring
    _ = (3 * 4 + 4) / 8 := by rw [h1, h2]
    _ = 2 := by ring

example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3 = ((a - 3)^2 + 6 * a - 9) - a + 3 := by ring
    _ = (a - 3)^2 + 5 * a - 6 := by ring
    _ = (a - 3)^2 + 5 * ((a - 3) + 3) - 6 := by ring
    _ = (a - 3)^2 + 5 * (a - 3) + 9 := by ring
    _ = (2 * b)^2 + 5 * (2 * b) + 9 := by rw [h1]
    _ = 4 * b ^ 2 + 10 * b + 9 := by ring

example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = (z^2 - z + 1) * (z^2 - 2) + 3 := by ring
    _ = (z^2 - z + 1) * 0 + 3 := by rw [h1]
    _ = 3 := by ring

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  calc
    y = 4 * x - 3 := by rw [h2]
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 9 := by ring

example {a b : ℤ} (h : a - b = 0) : a = b := by
  calc
    a = a - b + b := by ring
    _ = 0 + b := by rw [h]
    _ = b := by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x = x - 3 * y + 3 * y := by ring
    _ = 5 + 3 * y := by rw [h1]
    _ = 5 + 3 * 3 := by rw [h2]
    _ = 14 := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
    p = p - 2 * q + 2 * q := by ring
    _ = 1 + 2 * q := by rw [h1]
    _ = 1 + 2 * (-1) := by rw [h2]
    _ = -1 := by ring

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 := by
 calc
    x = x + 2 * y - 2 * y := by ring
    _ = 3 - 2 * y := by rw [h2]
    _ = 3 - 2 * (y + 1 - 1) := by ring
    _ = 3 - 2 * (3 - 1) := by rw [h1]
    _ = -1 := by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
    p = p + 4 * q - 4 * q := by ring
    _ = 1 - 4 * q := by rw [h1]
    _ = 1 - 4 * (q - 1 + 1) := by ring
    _ = 1 - 4 * (2 + 1) := by rw [h2]
    _ = -11 := by ring

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3) (h3 : c = 1) : a = 2 :=
  calc
    a = 7 - (2 * b + 3 * c)   := by rw [← h1]; ring
    _ = 7 - (2 * b + 3 * 1)   := by rw [h3]
    _ = 4 - 2 * b             := by ring
    _ = 4 - 2 * (3 - 2 * c)   := by rw [← h2]; ring
    _ = 4 - 2 * (3 - 2 * 1)   := by rw [h3]
    _ = 2                     := by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
    u = (4 * u + v - v) / 4 := by ring
    _ = (3 - 2) / 4 := by rw [h1, h2]
    _ = 1 / 4 := by ring

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by
  calc
    c = 4 * c + 1 - 3 * c + 2 -3 := by ring
    _ = 3 * c - 2 - 3 * c + 2 -3 := by rw [h1]
    _ = -3 := by ring

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]
