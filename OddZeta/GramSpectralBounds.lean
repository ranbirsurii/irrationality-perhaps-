import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OddZeta

noncomputable def gramEigenMin (A B C : ℝ) : ℝ :=
  (A + C - Real.sqrt ((C - A) ^ 2 + 4 * B ^ 2)) / 2

noncomputable def gramEigenMax (A B C : ℝ) : ℝ :=
  (A + C + Real.sqrt ((C - A) ^ 2 + 4 * B ^ 2)) / 2

theorem gram_eigenvalue_sum (A B C : ℝ) :
    gramEigenMin A B C + gramEigenMax A B C = A + C := by
  unfold gramEigenMin gramEigenMax
  ring

theorem gram_eigenvalue_product (A B C : ℝ) :
    gramEigenMin A B C * gramEigenMax A B C = A * C - B ^ 2 := by
  have h := Real.sq_sqrt (show 0 ≤ (C - A) ^ 2 + 4 * B ^ 2 by positivity)
  unfold gramEigenMin gramEigenMax
  nlinarith

theorem gram_eigenvalues_are_roots (A B C : ℝ) :
    (gramEigenMin A B C) ^ 2 - (A + C) * gramEigenMin A B C +
        (A * C - B ^ 2) = 0 ∧
    (gramEigenMax A B C) ^ 2 - (A + C) * gramEigenMax A B C +
        (A * C - B ^ 2) = 0 := by
  have hs := gram_eigenvalue_sum A B C
  have hp := gram_eigenvalue_product A B C
  constructor <;> rw [← hs, ← hp] <;> ring

theorem reduced_gram_eigenvalue_bounds (A B C : ℝ)
    (hA : 0 ≤ A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A) :
    A / 2 ≤ gramEigenMin A B C ∧ gramEigenMin A B C ≤ A ∧
      C ≤ gramEigenMax A B C ∧ gramEigenMax A B C ≤ 3 * C / 2 := by
  have hC : 0 ≤ C := hA.trans hAC
  have hBsq : 4 * B ^ 2 ≤ A ^ 2 := by
    have h := mul_self_le_mul_self (show 0 ≤ 2 * |B| by positivity) hB
    nlinarith [sq_abs B]
  have hdisc : (C - A) ^ 2 + 4 * B ^ 2 ≤ C ^ 2 := by
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hAC)]
  have hUpper : Real.sqrt ((C - A) ^ 2 + 4 * B ^ 2) ≤ C := by
    calc
      _ ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hdisc
      _ = C := Real.sqrt_sq hC
  have hLower : C - A ≤ Real.sqrt ((C - A) ^ 2 + 4 * B ^ 2) := by
    calc
      C - A = Real.sqrt ((C - A) ^ 2) :=
        (Real.sqrt_sq (sub_nonneg.mpr hAC)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg B])
  unfold gramEigenMin gramEigenMax
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem reduced_gram_trace_bounds (A C : ℝ) (hA : 0 ≤ A) (hAC : A ≤ C) :
    C ≤ A + C ∧ A + C ≤ 2 * C := by
  constructor <;> linarith

theorem reduced_gram_condition_number_bounds (A B C : ℝ)
    (hA : 0 < A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A) :
    C / A ≤ gramEigenMax A B C / gramEigenMin A B C ∧
      gramEigenMax A B C / gramEigenMin A B C ≤ 3 * C / A := by
  have h := reduced_gram_eigenvalue_bounds A B C hA.le hAC hB
  have hmin : 0 < gramEigenMin A B C := lt_of_lt_of_le (by linarith) h.1
  have hC : 0 ≤ C := hA.le.trans hAC
  have hmax : 0 ≤ gramEigenMax A B C := hC.trans h.2.2.1
  constructor
  · calc
      C / A ≤ gramEigenMax A B C / A := div_le_div_of_nonneg_right h.2.2.1 hA.le
      _ ≤ gramEigenMax A B C / gramEigenMin A B C :=
        div_le_div_of_nonneg_left hmax hmin h.2.1
  · calc
      _ ≤ (3 * C / 2) / gramEigenMin A B C :=
        div_le_div_of_nonneg_right h.2.2.2 hmin.le
      _ ≤ (3 * C / 2) / (A / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) h.1
      _ = 3 * C / A := by field_simp

theorem gram_larger_eigenvalue_le_det_div (A B C m : ℝ)
    (hA : 0 ≤ A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A)
    (hm : 0 < m) (hmin : m ≤ gramEigenMin A B C) :
    gramEigenMax A B C ≤ (A * C - B ^ 2) / m := by
  have hmax : 0 ≤ gramEigenMax A B C :=
    (hA.trans hAC).trans (reduced_gram_eigenvalue_bounds A B C hA hAC hB).2.2.1
  apply (le_div_iff₀ hm).mpr
  calc
    gramEigenMax A B C * m ≤ gramEigenMax A B C * gramEigenMin A B C :=
      mul_le_mul_of_nonneg_left hmin hmax
    _ = A * C - B ^ 2 := by rw [mul_comm, gram_eigenvalue_product]

theorem gram_cost_bound_from_eigenvalue (A B C P Γ K : ℝ)
    (hA : 0 ≤ A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A)
    (hP : 0 ≤ P) (hΓ : 0 < Γ)
    (hK : K ≤ P * Real.sqrt C / Γ) :
    K ≤ P * Real.sqrt (gramEigenMax A B C) / Γ := by
  have hμ := (reduced_gram_eigenvalue_bounds A B C hA hAC hB).2.2.1
  exact hK.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hμ) hP) hΓ.le)

theorem reduced_integer_gram_uniform_gap (A B C : ℝ)
    (hA : 1 ≤ A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A) :
    (1 : ℝ) / 2 ≤ gramEigenMin A B C := by
  have h := (reduced_gram_eigenvalue_bounds A B C (by linarith) hAC hB).1
  linarith

theorem reduced_integer_gram_max_le_twice_det (A B C : ℝ)
    (hA : 1 ≤ A) (hAC : A ≤ C) (hB : 2 * |B| ≤ A) :
    gramEigenMax A B C ≤ 2 * (A * C - B ^ 2) := by
  have h := gram_larger_eigenvalue_le_det_div A B C (1 / 2)
    (by linarith) hAC hB (by norm_num)
    (reduced_integer_gram_uniform_gap A B C hA hAC hB)
  linarith

end OddZeta
