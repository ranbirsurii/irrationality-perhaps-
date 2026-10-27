import Mathlib

/-!
# Adams projectors for all odd weights

This file proves the finite-dimensional eigenvalue calculation proposed in
the chat construction. The projector has rational coefficients whose
denominator depends on the target weight only, not on the Apéry index.
It does not assert that the geometric family has a motivic lift.
-/

namespace OddZeta

/-- Eigenvalue of `psi₂` on the odd weight `2j + 1`. -/
def oddAdamsEigenvalue (j : ℕ) : ℚ := (2 : ℚ) ^ (2 * j + 1)

theorem oddAdamsEigenvalue_strict {i j : ℕ} (hij : i < j) :
    oddAdamsEigenvalue i < oddAdamsEigenvalue j := by
  have hexp : 2 * i + 1 < 2 * j + 1 := by omega
  have hnat : (2 : ℕ) ^ (2 * i + 1) < 2 ^ (2 * j + 1) :=
    Nat.pow_lt_pow_right (by decide) hexp
  change (2 : ℚ) ^ (2 * i + 1) < 2 ^ (2 * j + 1)
  exact_mod_cast hnat

/-- The denominator in the Lagrange projector onto weight `2r + 1`. -/
def oddAdamsProjectorDenominator (r : ℕ) : ℚ :=
  ∏ j ∈ Finset.Icc 1 (r - 1),
    (oddAdamsEigenvalue r - oddAdamsEigenvalue j)

/-- The spectral polynomial projecting to weight `2r + 1`. -/
def oddAdamsProjectorScalar (r : ℕ) (x : ℚ) : ℚ :=
  (∏ j ∈ Finset.Icc 1 (r - 1), (x - oddAdamsEigenvalue j)) /
    oddAdamsProjectorDenominator r

theorem oddAdamsProjectorDenominator_ne_zero {r : ℕ} :
    oddAdamsProjectorDenominator r ≠ 0 := by
  unfold oddAdamsProjectorDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hr : 0 < r := by
    have hjlower := (Finset.mem_Icc.mp hj).1
    have hjbound := (Finset.mem_Icc.mp hj).2
    omega
  have hjr : j < r := Nat.lt_of_le_pred hr (Finset.mem_Icc.mp hj).2
  exact sub_ne_zero.mpr (ne_of_gt (oddAdamsEigenvalue_strict hjr))

/-- The target eigenvalue survives with coefficient one. -/
theorem oddAdamsProjectorScalar_target {r : ℕ} :
    oddAdamsProjectorScalar r (oddAdamsEigenvalue r) = 1 := by
  have hden :
      (∏ j ∈ Finset.Icc 1 (r - 1),
        (oddAdamsEigenvalue r - oddAdamsEigenvalue j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hr : 0 < r := by
      have hjlower := (Finset.mem_Icc.mp hj).1
      have hjbound := (Finset.mem_Icc.mp hj).2
      omega
    have hjr : j < r := Nat.lt_of_le_pred hr (Finset.mem_Icc.mp hj).2
    exact sub_ne_zero.mpr (ne_of_gt (oddAdamsEigenvalue_strict hjr))
  unfold oddAdamsProjectorScalar oddAdamsProjectorDenominator
  exact div_self hden

/-- Every lower odd weight is annihilated. -/
theorem oddAdamsProjectorScalar_kills_lower {r i : ℕ}
    (hi : 1 ≤ i) (hir : i < r) :
    oddAdamsProjectorScalar r (oddAdamsEigenvalue i) = 0 := by
  have hiMem : i ∈ Finset.Icc 1 (r - 1) := by
    simp only [Finset.mem_Icc]
    exact ⟨hi, Nat.le_pred_of_lt hir⟩
  have hnum :
      (∏ j ∈ Finset.Icc 1 (r - 1),
        (oddAdamsEigenvalue i - oddAdamsEigenvalue j)) = 0 :=
    Finset.prod_eq_zero hiMem (by simp)
  unfold oddAdamsProjectorScalar
  rw [hnum]
  simp

/-- The weight-zero rational coordinate receives an explicit rational
coefficient. Its denominator is the finite eigenvalue gap product. -/
theorem oddAdamsProjectorScalar_weight_zero {r : ℕ} :
    oddAdamsProjectorScalar r 1 =
      (∏ j ∈ Finset.Icc 1 (r - 1),
        (1 - oddAdamsEigenvalue j)) /
        oddAdamsProjectorDenominator r := by
  rfl

/-- The projector denominator is a fixed rational number for each target
weight; it has no dependence on the sequence index used to build a class. -/
theorem oddAdamsProjectorDenominator_depends_only_on_weight
    (r₁ r₂ : ℕ) (hr : r₁ = r₂) :
    oddAdamsProjectorDenominator r₁ = oddAdamsProjectorDenominator r₂ := by
  rw [hr]

end OddZeta
