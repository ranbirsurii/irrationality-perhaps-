import Mathlib
import OddZeta.AperyStructure
import OddZeta.AperyRegulatorGeometry

/-!
# The elliptic Picard--Fuchs regulator comparison, at operator level

This file makes the proposed comparison precise at the level justified by the
chat calculation: the level-six elliptic family and its marked section are
written explicitly, and the first Taylor coefficient of the Apéry K3
Picard--Fuchs residual is computed on an arbitrary regulator jet. The jet
calculation is formal and does not assert that a particular motivic cycle has
that jet; the geometric regulator/non-normal-function identity remains a
separate comparison statement.
-/

namespace OddZeta

def x16WeierstrassA (t : ℚ) : ℚ := ((t - 3) ^ 2 - 12) / 4

def x16WeierstrassRhs (t x : ℚ) : ℚ :=
  x * (x ^ 2 + x16WeierstrassA t * x + t)

def x16SectionX (t : ℚ) : ℚ := t

def x16SectionY (t : ℚ) : ℚ := t * (t - 1) / 2

/-- The displayed section lies on the universal `X₁(6)` elliptic cubic. -/
theorem x16Section_on_curve (t : ℚ) :
    x16WeierstrassRhs t (x16SectionX t) = (x16SectionY t) ^ 2 := by
  unfold x16WeierstrassRhs x16WeierstrassA x16SectionX x16SectionY
  ring

def x16PFLeading (t : ℚ) : ℚ := t * (t - 1) * (t - 9)

def x16PFDerivativeCoeff (t : ℚ) : ℚ := 3 * t ^ 2 - 20 * t + 9

def x16PFConstantCoeff (t : ℚ) : ℚ := t - 3

theorem x16PFLeading_derivative (t : ℚ) :
    (t - 1) * (t - 9) + t * (t - 9) + t * (t - 1) =
      x16PFDerivativeCoeff t := by
  unfold x16PFDerivativeCoeff
  ring

/-- Away from the four singular fibers, the level-six root coefficients are
exactly the normalized coefficients of the elliptic Picard--Fuchs equation
`d/dt(S(t) F') + (t-3)F = 0`. -/
theorem x16PF_normalized_derivative_coeff (t : ℚ)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht9 : t ≠ 9) :
    x16PFLeading t * levelSixRootP t =
      x16PFDerivativeCoeff t := by
  unfold x16PFLeading levelSixRootP x16PFDerivativeCoeff
  field_simp [ht0, sub_ne_zero.mpr (Ne.symm ht1),
    sub_ne_zero.mpr (Ne.symm ht9)]
  ring

theorem x16PF_normalized_constant_coeff (t : ℚ)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht9 : t ≠ 9) :
    x16PFLeading t * levelSixRootQ t = x16PFConstantCoeff t := by
  unfold x16PFLeading levelSixRootQ x16PFConstantCoeff
  field_simp [ht0, sub_ne_zero.mpr (Ne.symm ht1),
    sub_ne_zero.mpr (Ne.symm ht9)]

noncomputable def aperyK3Theta (p : Polynomial ℚ) : Polynomial ℚ :=
  Polynomial.X * p.derivative

/-- Kerr's Apéry K3 Picard--Fuchs operator in Euler-derivative form. -/
noncomputable def aperyK3PFPolynomialOperator (p : Polynomial ℚ) : Polynomial ℚ :=
  (Polynomial.X ^ 2 - 34 * Polynomial.X + 1) *
      aperyK3Theta (aperyK3Theta (aperyK3Theta p)) +
    2 * Polynomial.X * (Polynomial.X - 17) *
      aperyK3Theta (aperyK3Theta p) +
    3 * Polynomial.X * (Polynomial.X - 9) * aperyK3Theta p +
    Polynomial.X * (Polynomial.X - 5) * p

/-- The first coefficient of the Picard--Fuchs residual of a normal-function
jet `A + B t` is `B - 5 A`. -/
theorem aperyK3PF_first_regulator_jet (A B : ℚ) :
    (aperyK3PFPolynomialOperator
      (Polynomial.C A + Polynomial.C B * Polynomial.X)).coeff 1 = B - 5 * A := by
  have hθ : aperyK3Theta (Polynomial.C A + Polynomial.C B * Polynomial.X) =
      Polynomial.C B * Polynomial.X := by
    simp [aperyK3Theta]
  have hθ' : aperyK3Theta (Polynomial.C B * Polynomial.X) =
      Polynomial.C B * Polynomial.X := by
    simp [aperyK3Theta]
  rw [aperyK3PFPolynomialOperator, hθ, hθ', hθ']
  have hpoly :
      (Polynomial.X ^ 2 - 34 * Polynomial.X + 1) *
          (Polynomial.C B * Polynomial.X) +
        2 * Polynomial.X * (Polynomial.X - 17) *
          (Polynomial.C B * Polynomial.X) +
        3 * Polynomial.X * (Polynomial.X - 9) *
          (Polynomial.C B * Polynomial.X) +
        Polynomial.X * (Polynomial.X - 5) *
          (Polynomial.C A + Polynomial.C B * Polynomial.X) =
        Polynomial.C B * Polynomial.X -
          5 * Polynomial.C A * Polynomial.X +
          Polynomial.C A * Polynomial.X ^ 2 -
          100 * Polynomial.C B * Polynomial.X ^ 2 +
          7 * Polynomial.C B * Polynomial.X ^ 3 := by
    ring
  rw [hpoly]
  simp [Polynomial.coeff_mul_X_pow']

end OddZeta
