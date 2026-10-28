import OddZeta.OddHankelArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace OddZeta

noncomputable def growthBase (n : ℕ) : ℝ := (n : ℝ) + 1

theorem growthBase_pos (n : ℕ) : 0 < growthBase n := by
  unfold growthBase
  positivity

theorem growthBase_tendsto : Tendsto growthBase atTop atTop := by
  apply tendsto_atTop_mono _ (tendsto_natCast_atTop_atTop (R := ℝ))
  intro n
  change (n : ℝ) ≤ (n : ℝ) + 1
  linarith

theorem power_gap_limit (p d : ℝ) (hpd : p < d) :
    Tendsto (fun n : ℕ => growthBase n ^ p / growthBase n ^ d) atTop (nhds 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hpd)).comp growthBase_tendsto
  convert h using 1
  ext n
  rw [Function.comp_apply, show -(d - p) = p - d by ring,
    Real.rpow_sub (growthBase_pos n)]

theorem logarithmic_power_gap_limit (p d k : ℝ) (hpd : p < d) :
    Tendsto (fun n : ℕ =>
      growthBase n ^ p * Real.log (growthBase n) ^ k / growthBase n ^ d)
      atTop (nhds 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop k (sub_pos.mpr hpd)).tendsto_div_nhds_zero).comp growthBase_tendsto
  convert h using 1
  ext n
  rw [Function.comp_apply, Real.rpow_sub (growthBase_pos n)]
  field_simp

theorem quotient_zero_of_power_bounds (u D : ℕ → ℝ) (Cu Cd p d : ℝ)
    (hCd : 0 < Cd) (hpd : p < d)
    (hu : ∀ᶠ n in atTop, |u n| ≤ Cu * growthBase n ^ p)
    (hD : ∀ᶠ n in atTop, Cd * growthBase n ^ d ≤ D n) :
    Tendsto (fun n => u n / D n) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ =>
      (Cu / Cd) * (growthBase n ^ p / growthBase n ^ d)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (power_gap_limit p d hpd)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hu, hD] with n hn hd
  have hb := growthBase_pos n
  have hden : 0 < Cd * growthBase n ^ d := mul_pos hCd (Real.rpow_pos_of_pos hb _)
  have hDn : 0 < D n := lt_of_lt_of_le hden hd
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hDn]
  calc
    |u n| / D n ≤ |u n| / (Cd * growthBase n ^ d) :=
      div_le_div_of_nonneg_left (abs_nonneg _) hden hd
    _ ≤ (Cu * growthBase n ^ p) / (Cd * growthBase n ^ d) :=
      div_le_div_of_nonneg_right hn hden.le
    _ = (Cu / Cd) * (growthBase n ^ p / growthBase n ^ d) := by ring

theorem quotient_zero_of_log_power_bounds (u D : ℕ → ℝ) (Cu Cd p d k : ℝ)
    (hCd : 0 < Cd) (hpd : p < d)
    (hu : ∀ᶠ n in atTop,
      |u n| ≤ Cu * (growthBase n ^ p * Real.log (growthBase n) ^ k))
    (hD : ∀ᶠ n in atTop, Cd * growthBase n ^ d ≤ D n) :
    Tendsto (fun n => u n / D n) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ =>
      (Cu / Cd) * (growthBase n ^ p * Real.log (growthBase n) ^ k / growthBase n ^ d))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (logarithmic_power_gap_limit p d k hpd)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hu, hD] with n hn hd
  have hb := growthBase_pos n
  have hden : 0 < Cd * growthBase n ^ d := mul_pos hCd (Real.rpow_pos_of_pos hb _)
  have hDn : 0 < D n := lt_of_lt_of_le hden hd
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hDn]
  calc
    |u n| / D n ≤ |u n| / (Cd * growthBase n ^ d) :=
      div_le_div_of_nonneg_left (abs_nonneg _) hden hd
    _ ≤ (Cu * (growthBase n ^ p * Real.log (growthBase n) ^ k)) /
        (Cd * growthBase n ^ d) := div_le_div_of_nonneg_right hn hden.le
    _ = (Cu / Cd) *
        (growthBase n ^ p * Real.log (growthBase n) ^ k / growthBase n ^ d) := by ring

theorem shifted_height_denominator_lower (r n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    growthBase n ^ (4 * r) ≤
      growthBase n ^ (2 * r) * (growthBase n + a) ^ (2 * r) := by
  rw [show 4 * r = 2 * r + 2 * r by omega, pow_add]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (growthBase_pos n).le (le_add_of_nonneg_right ha) _)
    (pow_nonneg (growthBase_pos n).le _)

theorem shifted_height_zero_of_polynomial_bound (r : ℕ) (u a : ℕ → ℝ)
    (C p : ℝ) (hp : p < (4 * r : ℕ))
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hu : ∀ᶠ n in atTop, |u n| ≤ C * growthBase n ^ p) :
    Tendsto (fun n => u n /
      (growthBase n ^ (2 * r) * (growthBase n + a n) ^ (2 * r)))
      atTop (nhds 0) := by
  apply quotient_zero_of_power_bounds u _ C 1 p (4 * r : ℕ) (by norm_num) hp hu
  filter_upwards [ha] with n hn
  simpa only [one_mul, Real.rpow_natCast] using
    shifted_height_denominator_lower r n (a n) hn

theorem shifted_height_zero_of_log_polynomial_bound (r : ℕ) (u a : ℕ → ℝ)
    (C p k : ℝ) (hp : p < (4 * r : ℕ))
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hu : ∀ᶠ n in atTop,
      |u n| ≤ C * (growthBase n ^ p * Real.log (growthBase n) ^ k)) :
    Tendsto (fun n => u n /
      (growthBase n ^ (2 * r) * (growthBase n + a n) ^ (2 * r)))
      atTop (nhds 0) := by
  apply quotient_zero_of_log_power_bounds u _ C 1 p (4 * r : ℕ) k
    (by norm_num) hp hu
  filter_upwards [ha] with n hn
  simpa only [one_mul, Real.rpow_natCast] using
    shifted_height_denominator_lower r n (a n) hn

theorem shifted_height_denominator_power_lower (r n : ℕ) (a c β : ℝ)
    (hc : 0 < c) (ha : c * growthBase n ^ β ≤ growthBase n + a) :
    c ^ (2 * r) * growthBase n ^ ((2 * r : ℕ) + β * (2 * r : ℕ)) ≤
      growthBase n ^ (2 * r) * (growthBase n + a) ^ (2 * r) := by
  have hpower := pow_le_pow_left₀
    (mul_nonneg hc.le (Real.rpow_nonneg (growthBase_pos n).le β)) ha (2 * r)
  calc
    c ^ (2 * r) * growthBase n ^ ((2 * r : ℕ) + β * (2 * r : ℕ)) =
        growthBase n ^ (2 * r) * (c * growthBase n ^ β) ^ (2 * r) := by
      rw [Real.rpow_add (growthBase_pos n), Real.rpow_mul (growthBase_pos n).le]
      simp only [Real.rpow_natCast, mul_pow]
      ring
    _ ≤ growthBase n ^ (2 * r) * (growthBase n + a) ^ (2 * r) :=
      mul_le_mul_of_nonneg_left hpower (pow_nonneg (growthBase_pos n).le _)

theorem shifted_height_zero_of_log_bound_power_shift (r : ℕ) (u a : ℕ → ℝ)
    (C p k c β : ℝ) (hc : 0 < c) (hp : p < (2 * r : ℕ) + β * (2 * r : ℕ))
    (ha : ∀ᶠ n in atTop, c * growthBase n ^ β ≤ growthBase n + a n)
    (hu : ∀ᶠ n in atTop,
      |u n| ≤ C * (growthBase n ^ p * Real.log (growthBase n) ^ k)) :
    Tendsto (fun n => u n /
      (growthBase n ^ (2 * r) * (growthBase n + a n) ^ (2 * r)))
      atTop (nhds 0) := by
  apply quotient_zero_of_log_power_bounds u _ C (c ^ (2 * r)) p
    ((2 * r : ℕ) + β * (2 * r : ℕ)) k (pow_pos hc _) hp hu
  filter_upwards [ha] with n hn
  exact shifted_height_denominator_power_lower r n (a n) c β hc hn

theorem critical_logarithmic_limit (k : ℝ) (hk : k < 0) :
    Tendsto (fun n : ℕ => Real.log (growthBase n) ^ k) atTop (nhds 0) := by
  have h := (tendsto_rpow_neg_atTop (neg_pos.mpr hk)).comp
    (Real.tendsto_log_atTop.comp growthBase_tendsto)
  simpa only [neg_neg, Function.comp_def] using h

theorem quotient_zero_of_critical_log_bound (u D : ℕ → ℝ) (C k : ℝ) (hk : k < 0)
    (hD : ∀ᶠ n in atTop, 0 < D n)
    (hu : ∀ᶠ n in atTop, |u n| ≤ D n * (C * Real.log (growthBase n) ^ k)) :
    Tendsto (fun n => u n / D n) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => C * Real.log (growthBase n) ^ k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (critical_logarithmic_limit k hk)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hu, hD] with n hn hd
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  simpa only [mul_comm] using hn

end OddZeta
