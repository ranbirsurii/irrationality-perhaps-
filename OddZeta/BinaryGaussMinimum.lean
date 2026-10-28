import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OddZeta

def binaryQuadratic (A B C x y : ℝ) : ℝ := A * x ^ 2 + 2 * B * x * y + C * y ^ 2

theorem integer_square_ge_abs (z : ℤ) : |(z : ℝ)| ≤ (z : ℝ) ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hi : (1 : ℤ) ≤ |z| := by
    have h := abs_pos.mpr hz
    omega
  have hr : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast hi
  have hp := mul_nonneg (abs_nonneg (z : ℝ)) (show 0 ≤ |(z : ℝ)| - 1 by linarith)
  nlinarith [sq_abs (z : ℝ)]

theorem reduced_binary_cross_bound (A B x y : ℝ)
    (hB : 2 * |B| ≤ A) :
    -(A * |x| * |y|) ≤ 2 * B * x * y := by
  have hmul := mul_le_mul_of_nonneg_right hB (mul_nonneg (abs_nonneg x) (abs_nonneg y))
  have habs : |2 * B * x * y| ≤ A * |x| * |y| := by
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc] using hmul
  exact (neg_le_neg habs).trans (neg_abs_le (2 * B * x * y))

theorem reduced_binary_half_diagonal (A B C x y : ℝ)
    (hA : 0 ≤ A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A) :
    (A * x ^ 2 + C * y ^ 2) / 2 ≤ binaryQuadratic A B C x y := by
  have hcross := reduced_binary_cross_bound A B x y hB
  have hsq := mul_nonneg hA (sq_nonneg (|x| - |y|))
  have hdiff := mul_nonneg (sub_nonneg.mpr hAC) (sq_nonneg y)
  simp only [sub_sq, sq_abs] at hsq
  unfold binaryQuadratic
  nlinarith

theorem reduced_binary_second_coordinate_minimum (A B C : ℝ)
    (hA : 0 < A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A)
    (u v : ℤ) (hv : v ≠ 0) :
    C ≤ binaryQuadratic A B C u v := by
  have hC : 0 ≤ C := hA.le.trans hAC
  have hvabs : (1 : ℤ) ≤ |v| := by
    have h := abs_pos.mpr hv
    omega
  by_cases hone : |v| = 1
  · have hvreal : |(v : ℝ)| = 1 := by exact_mod_cast hone
    have hvSq : (v : ℝ) ^ 2 = 1 := by nlinarith [sq_abs (v : ℝ)]
    have hcross := reduced_binary_cross_bound A B u v hB
    rw [hvreal, mul_one] at hcross
    have hmul := mul_le_mul_of_nonneg_left (integer_square_ge_abs u) hA.le
    unfold binaryQuadratic
    rw [hvSq]
    nlinarith
  · have hvlarge : (2 : ℤ) ≤ |v| := by omega
    have hvlargeR : (2 : ℝ) ≤ |(v : ℝ)| := by exact_mod_cast hvlarge
    have hvSq : (4 : ℝ) ≤ (v : ℝ) ^ 2 := by nlinarith [sq_abs (v : ℝ)]
    have hmul := mul_nonneg hC (show 0 ≤ (v : ℝ) ^ 2 - 4 by linarith)
    have hfirst := mul_nonneg hA.le (sq_nonneg (u : ℝ))
    have hdiag := reduced_binary_half_diagonal A B C u v hA.le hAC hB
    nlinarith

theorem reduced_binary_first_minimum (A B C : ℝ)
    (hA : 0 < A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A)
    (u v : ℤ) (hnonzero : u ≠ 0 ∨ v ≠ 0) :
    A ≤ binaryQuadratic A B C u v := by
  by_cases hv : v = 0
  · have hu : u ≠ 0 := hnonzero.resolve_right (not_not.mpr hv)
    have hi : (1 : ℤ) ≤ |u| := by
      have h := abs_pos.mpr hu
      omega
    have hr : (1 : ℝ) ≤ |(u : ℝ)| := by exact_mod_cast hi
    have hs : (1 : ℝ) ≤ (u : ℝ) ^ 2 := hr.trans (integer_square_ge_abs u)
    simpa [binaryQuadratic, hv] using mul_le_mul_of_nonneg_left hs hA.le
  · exact hAC.trans (reduced_binary_second_coordinate_minimum A B C hA hAC hB u v hv)

theorem reduced_binary_independent_pair_minimum (A B C : ℝ)
    (hA : 0 < A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A)
    (u v w z : ℤ) (hdet : u * z - v * w ≠ 0) :
    C ≤ max (binaryQuadratic A B C u v) (binaryQuadratic A B C w z) := by
  by_cases hv : v = 0
  · have hz : z ≠ 0 := by
      intro h
      exact hdet (by simp [hv, h])
    exact (reduced_binary_second_coordinate_minimum A B C hA hAC hB w z hz).trans
      (le_max_right _ _)
  · exact (reduced_binary_second_coordinate_minimum A B C hA hAC hB u v hv).trans
      (le_max_left _ _)

theorem reduced_binary_coordinate_attainment (A B C : ℝ) :
    binaryQuadratic A B C 1 0 = A ∧ binaryQuadratic A B C 0 1 = C := by
  constructor <;> simp [binaryQuadratic]

theorem reduced_binary_transference_squared (A B C : ℝ)
    (hA : 0 < A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A) :
    0 < A * C - B ^ 2 ∧
      1 ≤ A * C / (A * C - B ^ 2) ∧
      A * C / (A * C - B ^ 2) ≤ 4 / 3 := by
  have hC : 0 < C := hA.trans_le hAC
  have hBsq : 4 * B ^ 2 ≤ A ^ 2 := by
    have h := mul_self_le_mul_self (show 0 ≤ 2 * |B| by positivity) hB
    nlinarith [sq_abs B]
  have hAA : A ^ 2 ≤ A * C := by nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hAC)]
  have hprod : 0 < A * C := mul_pos hA hC
  have hdet : 0 < A * C - B ^ 2 := by nlinarith
  refine ⟨hdet, ?_, ?_⟩
  · apply (le_div_iff₀ hdet).mpr
    nlinarith [sq_nonneg B]
  · apply (div_le_iff₀ hdet).mpr
    nlinarith

theorem reduced_binary_cost_sandwich (mu beta nu H2 delta : ℝ)
    (hmu : 0 < mu) (horder : mu ≤ nu) (hbeta : 2 * |beta| ≤ mu)
    (hdelta : delta ≠ 0) (hidentity : mu * nu - beta ^ 2 = delta ^ 2 * H2) :
    H2 / mu ≤ nu / delta ^ 2 ∧ nu / delta ^ 2 ≤ 4 * H2 / (3 * mu) := by
  have h := reduced_binary_transference_squared mu beta nu hmu horder hbeta
  have hd : 0 < delta ^ 2 := sq_pos_of_ne_zero hdelta
  constructor
  · apply (div_le_div_iff₀ hmu hd).mpr
    nlinarith [sq_nonneg beta]
  · apply (div_le_div_iff₀ hd (by positivity : 0 < 3 * mu)).mpr
    have hbound := (div_le_iff₀ h.1).mp h.2.2
    nlinarith

end OddZeta
