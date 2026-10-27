import OddZeta.AperyDeformation
import OddZeta.IrrationalityCriterion

namespace OddZeta

theorem aperyDeformationCoefficient_at_zero_index (m : ℕ) (t : ℚ) :
    aperyDeformationCoefficient 0 m t = (-1 : ℚ) ^ m / t ^ (2 * m + 2) := by
  simp only [aperyDeformationCoefficient, aperyDeformationSeries,
    coeff_quadraticInverseSeries, div_pow, div_div]
  rw [← pow_mul, ← pow_add]

noncomputable def aperyZeroCoefficientReal (m : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ m / t ^ (2 * m + 2)

theorem aperyZeroCoefficientReal_eq_cast (m : ℕ) (t : ℚ) :
    aperyZeroCoefficientReal m (t : ℝ) = (aperyDeformationCoefficient 0 m t : ℝ) := by
  rw [aperyDeformationCoefficient_at_zero_index]
  simp [aperyZeroCoefficientReal]

noncomputable def aperyZeroPushforwardSummand (m : ℕ) (t : ℝ) : ℝ :=
  ((2 * m + 2 : ℕ) : ℝ) * (-1 : ℝ) ^ m / t ^ (2 * m + 3)

theorem aperyZeroCoefficientReal_hasDerivAt (m : ℕ) (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (aperyZeroCoefficientReal m)
      (-aperyZeroPushforwardSummand m t) t := by
  have h := (hasDerivAt_zpow (-((2 * m + 2 : ℕ) : ℤ)) t (Or.inl ht)).const_mul
    ((-1 : ℝ) ^ m)
  have hexp : -((2 * m + 2 : ℕ) : ℤ) - 1 = -((2 * m + 3 : ℕ) : ℤ) := by omega
  rw [hexp] at h
  simp only [zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast] at h
  convert! h using 1
  simp [aperyZeroPushforwardSummand, div_eq_mul_inv]
  ring

theorem oddZetaValue_eq_tsum_inv_pow (k : ℕ) (hk : 1 ≤ k) :
    oddZetaValue k = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * k + 1) := by
  have hs : 1 < (((2 * k + 1 : ℕ) : ℂ)).re := by
    norm_num
    omega
  have hz : riemannZeta ((2 * k + 1 : ℕ) : ℂ) =
      ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * k + 1) : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp only [Complex.cpow_natCast]
    push_cast
    rfl
  simpa [oddZetaValue] using congrArg Complex.re hz

theorem aperyZeroPushforward_summable (m : ℕ) :
    Summable (fun n : ℕ => aperyZeroPushforwardSummand m ((n : ℝ) + 1)) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * m + 3)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hs' := (summable_nat_add_iff 1).mpr hs
  simpa [aperyZeroPushforwardSummand, div_eq_mul_inv, mul_assoc] using
    hs'.mul_left (((2 * m + 2 : ℕ) : ℝ) * (-1 : ℝ) ^ m)

theorem aperyZeroPushforward_eq_oddZeta (m : ℕ) :
    (∑' n : ℕ, aperyZeroPushforwardSummand m ((n : ℝ) + 1)) =
      ((2 * m + 2 : ℕ) : ℝ) * (-1 : ℝ) ^ m * oddZetaValue (m + 1) := by
  have hz := oddZetaValue_eq_tsum_inv_pow (m + 1) (by omega)
  have he : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
  rw [he] at hz
  calc
    _ = (((2 * m + 2 : ℕ) : ℝ) * (-1 : ℝ) ^ m) *
        (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * m + 3)) := by
          simp [aperyZeroPushforwardSummand, div_eq_mul_inv, tsum_mul_left, mul_assoc]
    _ = _ := by rw [← hz]

end OddZeta
