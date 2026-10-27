import Mathlib

/-!
# Apéry and marked elliptic data

This file records algebraic identities from the supplied note. The estimates
needed to prove irrationality of every odd zeta value are not consequences of
the period identities; they must be proved separately and are therefore kept
as explicit hypotheses in `IrrationalityCriterion`.
-/

namespace OddZeta

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
