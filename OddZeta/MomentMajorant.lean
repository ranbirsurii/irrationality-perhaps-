import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter

namespace OddZeta

theorem moment_cost_common_factor_invariant (D mu nu h : ℝ) (hh : h ≠ 0) :
    (D/h)^2 * mu * (h^2*nu) = D^2*mu*nu := by
  field_simp


theorem reduced_moment_quadratic_bound (a b v h k : ℝ)
    (ha : a ≤ v) (hb : 2 * |b| ≤ v) :
    a*h^2+2*b*h*k+v*k^2 ≤ (3/2:ℝ)*v*(h^2+k^2) := by
  have hv : 0 ≤ v := (by positivity : 0 ≤ 2*|b|).trans hb
  have hcross : 2*b*h*k ≤ |b| * (h^2+k^2) := by
    have h1 := neg_abs_le b
    have h2 := le_abs_self b
    by_cases hh : 0 ≤ h*k
    · nlinarith [sq_nonneg (h-k)]
    · nlinarith [sq_nonneg (h+k)]
  nlinarith [sq_nonneg h, sq_nonneg k]

theorem shifted_polynomial_exp_limit (C k alpha : ℝ) (ha : 0 < alpha) :
    Tendsto (fun n : ℕ => C*((n:ℝ)+1)^k*Real.exp (-alpha*(n:ℝ)))
      atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ)+1)
      tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k alpha ha).comp hx
  have hm := ht.const_mul (C*Real.exp alpha)
  simpa only [mul_zero] using hm.congr (fun n => by
    dsimp
    calc
      _ = C*((n:ℝ)+1)^k * (Real.exp alpha * Real.exp (-alpha*((n:ℝ)+1))) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring)

theorem moment_rhs_limit_of_majorant (R : ℕ → ℝ) (C k alpha : ℝ)
    (ha : 0 < alpha) (hR : ∀ᶠ n in atTop, 0 ≤ R n)
    (hbound : ∀ᶠ n in atTop,
      R n ≤ C*((n:ℝ)+1)^k*Real.exp (-alpha*(n:ℝ))) :
    Tendsto R atTop (nhds 0) := by
  exact squeeze_zero' hR hbound (shifted_polynomial_exp_limit C k alpha ha)

end OddZeta
