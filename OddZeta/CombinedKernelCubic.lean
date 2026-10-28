import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OddZeta

def combinedCubic (a b c w x y z u : ℝ) : ℝ :=
  w * (u-a) * (u-b) * (u-c) + x * (u-a) * (u-b) + y * (u-a) + z

theorem combined_cubic_expansion (a b c w x y z u : ℝ) :
    combinedCubic a b c w x y z u = w*u^3 +
      (x-w*(a+b+c))*u^2 + (w*(a*b+a*c+b*c)-x*(a+b)+y)*u +
      (-w*a*b*c+x*a*b-y*a+z) := by
  unfold combinedCubic
  ring

theorem quadratic_pair_factor (n t v : ℝ) :
    (t-v)*(t+n+v) = t*(t+n)-v*(n+v) := by ring

theorem combined_cubic_reflection (a b c w x y z n t : ℝ) :
    combinedCubic a b c w x y z ((-n-t)*((-n-t)+n)) =
      combinedCubic a b c w x y z (t*(t+n)) := by
  have h : (-n-t)*((-n-t)+n) = t*(t+n) := by ring
  rw [h]

theorem combined_cubic_coefficients_injective (a b c w x y z : ℝ)
    (h3 : w = 0) (h2 : x-w*(a+b+c) = 0)
    (h1 : w*(a*b+a*c+b*c)-x*(a+b)+y = 0)
    (h0 : -w*a*b*c+x*a*b-y*a+z = 0) :
    w = 0 ∧ x = 0 ∧ y = 0 ∧ z = 0 := by
  simp only [h3, zero_mul, sub_zero] at h2
  simp only [h3, h2, zero_mul, sub_zero, zero_add] at h1
  simp only [h3, h2, h1, neg_zero, zero_mul, zero_add, zero_sub] at h0
  exact ⟨h3,h2,h1,h0⟩

theorem cubic_absolute_majorant (a b c d u : ℝ) :
    |a*u^3+b*u^2+c*u+d| ≤
      |a| * |u|^3+|b| * |u|^2+|c| * |u|+|d| := by
  have h1 := abs_add_le (a*u^3+b*u^2+c*u) d
  have h2 := abs_add_le (a*u^3+b*u^2) (c*u)
  have h3 := abs_add_le (a*u^3) (b*u^2)
  simp only [abs_mul, abs_pow] at h1 h2 h3
  linarith

end OddZeta
