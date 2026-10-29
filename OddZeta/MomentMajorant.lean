import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter

namespace OddZeta

theorem weighted_gram_double_sum {ι : Type*} (I : Finset ι) (w p q : ι → ℝ) :
    (∑ i ∈ I, w i * p i ^ 2) * (∑ i ∈ I, w i * q i ^ 2) -
      (∑ i ∈ I, w i * p i * q i) ^ 2 =
    (1/2:ℝ) * ∑ i ∈ I, ∑ j ∈ I,
      w i * w j * (p i * q j - q i * p j) ^ 2 := by
  have hs : (∑ i ∈ I, ∑ j ∈ I, w i*w j*(p i*q j-q i*p j)^2) =
      2*((∑ i ∈ I, w i*p i^2)*(∑ j ∈ I, w j*q j^2)-
        (∑ i ∈ I, w i*p i*q i)^2) := by
    calc
      _ = ∑ i ∈ I, ∑ j ∈ I,
          ((w i*p i^2)*(w j*q j^2)+(w i*q i^2)*(w j*p j^2)-
            2*(w i*p i*q i)*(w j*p j*q j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [← Finset.sum_mul]
        ring_nf
        simp only [← Finset.sum_mul]
        ring
  rw [hs]
  ring

theorem log_scalar_cost (mu d a : ℝ) (hm : 0 < mu) (hd : 0 < d) (ha : 0 < a) :
    Real.log (mu*d/a) = Real.log mu + Real.log d - Real.log a := by
  rw [Real.log_div (mul_ne_zero hm.ne' hd.ne') ha.ne', Real.log_mul hm.ne' hd.ne']

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

theorem sandwich_limit_of_log_rate (C R : ℕ → ℝ) (delta : ℝ)
    (hd : 0 < delta) (hC : ∀ᶠ n in atTop, 0 < C n)
    (hlog : ∀ᶠ n in atTop, Real.log (C n) ≤ -delta*(n:ℝ))
    (hR : ∀ᶠ n in atTop, 0 ≤ R n)
    (hsand : ∀ᶠ n in atTop, R n ≤ (4/3:ℝ)*C n) :
    Tendsto R atTop (nhds 0) := by
  apply moment_rhs_limit_of_majorant R (4/3) 0 delta hd hR
  filter_upwards [hC,hlog,hsand] with n hc hl hs
  have he : C n ≤ Real.exp (-delta*(n:ℝ)) := by
    calc
      C n = Real.exp (Real.log (C n)) := (Real.exp_log hc).symm
      _ ≤ _ := Real.exp_le_exp.mpr hl
  simpa only [Real.rpow_zero,mul_one] using
    hs.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 4/3))

end OddZeta
