import OddZeta.PoisedKernelPositivity
import OddZeta.SymmetricPadePeriods

namespace OddZeta

def poisedFiveCombined (t : ℚ) : ℚ :=
  601088 * poisedRationalKernel 2 2 2 t + 37632 * poisedRationalKernel 2 2 3 t

theorem poisedFiveCombined_kernel (t : ℚ) (ht : t ≠ 0)
    (ht1 : t + 1 ≠ 0) (ht2 : t + 2 ≠ 0) :
    poisedFiveCombined t =
      256 * (147 * t ^ 2 + 294 * t + 143) *
        (t - 1) * (t - 2) * (t + 3) * (t + 4) /
          (t ^ 5 * (t + 1) ^ 5 * (t + 2) ^ 5) := by
  simp only [poisedFiveCombined, poisedRationalKernel,
    show Nat.mod 2 2 = 0 from rfl, pow_zero, one_mul]
  norm_num [Finset.prod_range_succ]
  field_simp
  ring

noncomputable def poisedFivePartial (t : ℝ) : ℝ :=
  5797120 / (t * (t + 1) * (t + 2)) +
    (-1449280 / t ^ 2 + 1449280 / (t + 2) ^ 2) +
    (591872 / t ^ 3 - 1183744 / (t + 1) ^ 3 + 591872 / (t + 2) ^ 3) +
    (-174640 / t ^ 4 + 174640 / (t + 2) ^ 4) +
    (27456 / t ^ 5 + 36864 / (t + 1) ^ 5 + 27456 / (t + 2) ^ 5)

theorem poisedFiveCombined_partial_fractions (t : ℚ) (ht : t ≠ 0)
    (ht1 : t + 1 ≠ 0) (ht2 : t + 2 ≠ 0) :
    (poisedFiveCombined t : ℝ) = poisedFivePartial (t : ℝ) := by
  rw [poisedFiveCombined_kernel t ht ht1 ht2]
  have h0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have h1 : (t : ℝ) + 1 ≠ 0 := by exact_mod_cast ht1
  have h2 : (t : ℝ) + 2 ≠ 0 := by exact_mod_cast ht2
  push_cast
  unfold poisedFivePartial
  field_simp
  ring

theorem consecutive_three_hasSum :
    HasSum (fun n : ℕ =>
      1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) (1 / 4 : ℝ) := by
  have h := mellin_rational_hasSum (fun i : Fin 3 => i.val) Fin.val_injective
  have hv : mellinRationalMoment (fun i : Fin 3 => i.val) = 1 / 4 := by
    decide +kernel
  rw [hv] at h
  convert! h using 1 <;>
    simp [Fin.prod_univ_succ, Nat.cast_add, Nat.cast_one, mul_assoc, one_div]
  funext n
  ring

theorem poisedFiveCombined_hasSum :
    HasSum (fun n : ℕ => (poisedFiveCombined ((n + 1 : ℕ) : ℚ) : ℝ))
      (91776 * mellinZetaValue 3 - 95165) := by
  have h := ((((consecutive_three_hasSum.mul_left 5797120).add
      (((mellin_zeta_hasSum 0).mul_left (-1449280)).add
        ((mellin_zeta_tail_hasSum 0 2).mul_left 1449280))).add
      ((((mellin_zeta_hasSum 1).mul_left 591872).sub
        ((mellin_zeta_tail_hasSum 1 1).mul_left 1183744)).add
          ((mellin_zeta_tail_hasSum 1 2).mul_left 591872))).add
      (((mellin_zeta_hasSum 2).mul_left (-174640)).add
        ((mellin_zeta_tail_hasSum 2 2).mul_left 174640))).add
      ((((mellin_zeta_hasSum 3).mul_left 27456).add
        ((mellin_zeta_tail_hasSum 3 1).mul_left 36864)).add
          ((mellin_zeta_tail_hasSum 3 2).mul_left 27456))
  have hv :
      5797120 * (1 / 4 : ℝ) +
        (-1449280 * mellinZetaValue 0 +
          1449280 * (mellinZetaValue 0 - (harmonicPower 2 2 : ℝ))) +
        (591872 * mellinZetaValue 1 -
          1183744 * (mellinZetaValue 1 - (harmonicPower 3 1 : ℝ)) +
          591872 * (mellinZetaValue 1 - (harmonicPower 3 2 : ℝ))) +
        (-174640 * mellinZetaValue 2 +
          174640 * (mellinZetaValue 2 - (harmonicPower 4 2 : ℝ))) +
        (27456 * mellinZetaValue 3 +
          36864 * (mellinZetaValue 3 - (harmonicPower 5 1 : ℝ)) +
          27456 * (mellinZetaValue 3 - (harmonicPower 5 2 : ℝ))) =
        91776 * mellinZetaValue 3 - 95165 := by
    norm_num [harmonicPower]
    ring
  rw [hv] at h
  apply h.congr_fun
  intro n
  rw [poisedFiveCombined_partial_fractions _ (by positivity) (by positivity) (by positivity)]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
  norm_num [poisedFivePartial, add_assoc]
  field_simp

theorem poisedFiveCombined_positive : 0 < 91776 * mellinZetaValue 3 - 95165 := by
  apply hasSum_pos_of_nonneg_of_pos _ _ poisedFiveCombined_hasSum
  · intro k
    have h2 := poisedRationalKernel_nonneg_integer 2 2 2 k
    have h3 := poisedRationalKernel_nonneg_integer 2 2 3 k
    change 0 ≤ ((601088 * poisedRationalKernel 2 2 2 _ +
      37632 * poisedRationalKernel 2 2 3 _ : ℚ) : ℝ)
    exact_mod_cast (add_nonneg (mul_nonneg (by norm_num) h2)
      (mul_nonneg (by norm_num) h3))
  · have h2 := poisedRationalKernel_pos_integer 2 2 2 2 (by omega)
    have h3 := poisedRationalKernel_nonneg_integer 2 2 3 2
    change 0 < ((601088 * poisedRationalKernel 2 2 2 _ +
      37632 * poisedRationalKernel 2 2 3 _ : ℚ) : ℝ)
    exact_mod_cast (add_pos_of_pos_of_nonneg (mul_pos (by norm_num) h2)
      (mul_nonneg (by norm_num) h3))

end OddZeta
