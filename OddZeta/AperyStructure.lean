import Mathlib

/-!
# Apéry and marked elliptic data

This file records algebraic identities from the supplied note. The estimates
needed to prove irrationality of every odd zeta value are not consequences of
the period identities; they must be proved separately and are therefore kept
as explicit hypotheses in `IrrationalityCriterion`.
-/

namespace OddZeta

/-! The symmetric-square coefficient identities are stated over `ℚ(x)` by
writing the formal derivatives of the rational coefficients explicitly. -/

def aperyDelta (x : ℚ) : ℚ := x ^ 2 - 34 * x + 1

def aperyRootP (x : ℚ) : ℚ :=
  (2 * x ^ 2 - 51 * x + 1) / (x * aperyDelta x)

def aperyRootQ (x : ℚ) : ℚ :=
  (x - 10) / (4 * x * aperyDelta x)

def aperyRootPPrime (x : ℚ) : ℚ :=
  ((4 * x - 51) * (x * aperyDelta x) -
      (2 * x ^ 2 - 51 * x + 1) * (3 * x ^ 2 - 68 * x + 1)) /
    (x * aperyDelta x) ^ 2

def aperyRootQPrime (x : ℚ) : ℚ :=
  (4 * x * aperyDelta x -
      4 * (x - 10) * (3 * x ^ 2 - 68 * x + 1)) /
    (4 * x * aperyDelta x) ^ 2

theorem apery_symmetric_square_second_coefficient (x : ℚ) :
    3 * aperyRootP x =
      3 * (2 * x ^ 2 - 51 * x + 1) / (x * aperyDelta x) := by
  change 3 * ((2 * x ^ 2 - 51 * x + 1) / (x * aperyDelta x)) = _
  rw [← mul_div_assoc]

theorem apery_symmetric_square_first_coefficient
    (x : ℚ) (hx : x ≠ 0) (hΔ : aperyDelta x ≠ 0) :
    aperyRootPPrime x + 4 * aperyRootQ x +
        2 * (aperyRootP x) ^ 2 =
      (1 - 112 * x + 7 * x ^ 2) / (x ^ 2 * aperyDelta x) := by
  have hΔfact : x * (x - 34) + 1 ≠ 0 := by
    rw [show x * (x - 34) + 1 = aperyDelta x by
      unfold aperyDelta
      ring]
    exact hΔ
  unfold aperyRootPPrime aperyRootP aperyRootQ aperyDelta
  field_simp [hx, hΔfact]
  ring

theorem apery_symmetric_square_constant_coefficient
    (x : ℚ) (hx : x ≠ 0) (hΔ : aperyDelta x ≠ 0) :
    2 * aperyRootQPrime x + 4 * aperyRootP x * aperyRootQ x =
      (x - 5) / (x ^ 2 * aperyDelta x) := by
  have hΔfact : x * (x - 34) + 1 ≠ 0 := by
    rw [show x * (x - 34) + 1 = aperyDelta x by
      unfold aperyDelta
      ring]
    exact hΔ
  unfold aperyRootQPrime aperyRootP aperyRootQ aperyDelta
  field_simp [hx, hΔfact]
  ring

/- The level-six coordinate is rational in `r`. -/
noncomputable def levelSixX (r : ℝ) : ℝ := r * (1 - 9 * r) / (1 - r)

theorem levelSixX_cleared (r : ℝ) (h : r ≠ 1) :
    levelSixX r * (1 - r) = r * (1 - 9 * r) := by
  unfold levelSixX
  have hd : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp [hd]

theorem branch_numerator_zero (s : ℝ) (hs : s ^ 2 = 2) :
    1 - 18 * (1 + 2 * s / 3) + 9 * (1 + 2 * s / 3) ^ 2 = 0 ∧
    1 - 18 * (1 - 2 * s / 3) + 9 * (1 - 2 * s / 3) ^ 2 = 0 := by
  constructor <;> nlinarith [hs]

theorem levelSix_branch_values (s : ℝ) (hs : s ^ 2 = 2) :
    levelSixX (1 + 2 * s / 3) = 17 + 12 * s ∧
    levelSixX (1 - 2 * s / 3) = 17 - 12 * s := by
  constructor
  · unfold levelSixX
    have hd : 1 - (1 + 2 * s / 3) ≠ 0 := by nlinarith [hs]
    rw [div_eq_iff hd]
    field_simp
    nlinarith [hs]
  · unfold levelSixX
    have hd : 1 - (1 - 2 * s / 3) ≠ 0 := by nlinarith [hs]
    rw [div_eq_iff hd]
    field_simp
    nlinarith [hs]

theorem apery_discriminant_factorization (s x : ℝ) (hs : s ^ 2 = 2) :
    x ^ 2 - 34 * x + 1 = (x - (17 + 12 * s)) * (x - (17 - 12 * s)) := by
  nlinarith [hs]

end OddZeta
