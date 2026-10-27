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

def x16LegendreLambda (α β : ℚ) : ℚ := (β - α) / β

def x16LegendreModulus (α β : ℚ) : ℚ := β / (β - α)

/-- In the Legendre cubic coordinate, this is the marked section's x-coordinate.
It is the algebraic characteristic of the associated third-kind period. -/
def x16LegendreCharacteristic (α β : ℚ) : ℚ := (β - 1) / (β - α)

def x16LegendreX (α β x : ℚ) : ℚ :=
  β * (x - α) / (x * (β - α))

def legendreCubic (m z : ℚ) : ℚ := z * (z - 1) * (z - m)

/-- A two-point zero-cycle, retaining its coefficients at the marked point
and at the identity. -/
structure TwoPointZeroCycle where
  markedCoefficient : ℤ
  originCoefficient : ℤ

def cycleDegree (C : TwoPointZeroCycle) : ℤ :=
  C.markedCoefficient + C.originCoefficient

def cycleAbelSum {G : Type} [AddCommGroup G] (C : TwoPointZeroCycle)
    (P : G) : G := C.markedCoefficient • P + C.originCoefficient • (0 : G)

/-- The cycle in the chat's one-motive `[Z -> E]`, `1 |-> P - O`. -/
def markedAbelCycle : TwoPointZeroCycle := ⟨1, -1⟩

theorem markedAbelCycle_degree_zero : cycleDegree markedAbelCycle = 0 := by
  rfl

theorem markedAbelCycle_abel_sum {G : Type} [AddCommGroup G] (P : G) :
    cycleAbelSum markedAbelCycle P = P := by
  simp [cycleAbelSum, markedAbelCycle]

/-- Abel summation of a two-point cycle is natural under an induced map of
additive realizations. This is the functoriality needed when a geometric
correspondence induces a map on the realization of the marked cycle. -/
theorem cycleAbelSum_inducedMap {G H : Type} [AddCommGroup G]
    [AddCommGroup H] (C : TwoPointZeroCycle) (φ : G →+ H) (P : G) :
    cycleAbelSum C (φ P) = φ (cycleAbelSum C P) := by
  simp [cycleAbelSum, map_zsmul]

/-- In particular, every induced homomorphism sends the marked one-motive
cycle to the image of its marked point. The theorem is abstract: it does not
construct a correspondence from the Apéry family to the elliptic curve. -/
theorem markedAbelCycle_inducedMap {G H : Type} [AddCommGroup G]
    [AddCommGroup H] (φ : G →+ H) (P : G) :
    cycleAbelSum markedAbelCycle (φ P) = φ P := by
  rw [markedAbelCycle_abel_sum]

/-- The coefficient multiplying `dx/(x-ν)` in the proposed third-kind form
`(Y+κ) dx / (2 (x-ν) Y)`. -/
def markedThirdKindResidueCoefficient (κ Y : ℚ) : ℚ :=
  (Y + κ) / (2 * Y)

theorem markedThirdKind_residue_at_P (κ : ℚ) (hκ : κ ≠ 0) :
    markedThirdKindResidueCoefficient κ κ = 1 := by
  unfold markedThirdKindResidueCoefficient
  field_simp [hκ]
  ring

theorem markedThirdKind_cancels_conjugate_pole (κ : ℚ) :
    markedThirdKindResidueCoefficient κ (-κ) = 0 := by
  unfold markedThirdKindResidueCoefficient
  simp

theorem x16_marked_characteristic (t α β : ℚ)
    (hprod : α * β = t) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hsep : β ≠ α) :
    x16LegendreX α β (x16SectionX t) =
      x16LegendreCharacteristic α β := by
  unfold x16LegendreX x16LegendreCharacteristic x16SectionX
  rw [← hprod]
  field_simp [hα, hβ, sub_ne_zero.mpr hsep]

/-- The Möbius coordinate above sends the marked Weierstrass point to the
Legendre characteristic; the inverse map is `x = α/(1-λz)`. -/
theorem x16_legendre_coordinate_inverse (α β z : ℚ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hsep : β ≠ α)
    (hden : 1 - x16LegendreLambda α β * z ≠ 0) :
    x16LegendreX α β
        (α / (1 - x16LegendreLambda α β * z)) = z := by
  have hden' : 1 - (β - α) / β * z ≠ 0 := by
    simpa [x16LegendreLambda] using hden
  have hdenprod : β - (β - α) * z ≠ 0 := by
    intro hz
    apply hden'
    field_simp [hβ]
    nlinarith [hz]
  have hden'' : β - β * z + α * z ≠ 0 := by
    have heq : β - β * z + α * z = β - (β - α) * z := by ring
    rw [heq]
    exact hdenprod
  unfold x16LegendreX x16LegendreLambda
  field_simp [hα, hβ, sub_ne_zero.mpr hsep, hden'']
  ring

/-- Root-parameter form of the Weierstrass-to-Legendre substitution. -/
theorem weierstrass_root_cubic_to_legendre (α β lam m z : ℚ)
    (hroot : β * lam = β - α) (hmod : lam * m = 1)
    (hden : 1 - lam * z ≠ 0) :
    (α / (1 - lam * z)) *
        (α / (1 - lam * z) - α) *
        (α / (1 - lam * z) - β) * (1 - lam * z) ^ 4 =
      -(α ^ 2 * β * lam ^ 3) * legendreCubic m z := by
  have hα : α - β = -(β * lam) := by linarith [hroot]
  have hdenfactor : 1 - lam * z = -(lam * (z - m)) := by
    calc
      1 - lam * z = lam * m - lam * z := by rw [hmod]
      _ = -(lam * (z - m)) := by ring
  have hleft : α / (1 - lam * z) - α = α * lam * z / (1 - lam * z) := by
    field_simp [hden]
    ring
  have hnum : α - (1 - lam * z) * β = lam * β * (z - 1) := by
    calc
      α - (1 - lam * z) * β = (α - β) + β * lam * z := by ring
      _ = lam * β * (z - 1) := by linear_combination hroot
  have hright : α / (1 - lam * z) - β = lam * β * (z - 1) / (1 - lam * z) := by
    field_simp [hden]
    exact hnum
  rw [hleft, hright, hdenfactor]
  unfold legendreCubic
  field_simp [hden]

/-- The roots of the `X₁(6)` cubic give the exact Legendre cubic and twist. -/
theorem x16_weierstrass_to_legendre (t α β z : ℚ)
    (hA : x16WeierstrassA t = -(α + β))
    (ht : α * β = t) (hβ : β ≠ 0)
    (hsep : β ≠ α)
    (hden : 1 - x16LegendreLambda α β * z ≠ 0) :
    x16WeierstrassRhs t
        (α / (1 - x16LegendreLambda α β * z)) *
        (1 - x16LegendreLambda α β * z) ^ 4 =
      -(α ^ 2 * β * (x16LegendreLambda α β) ^ 3) *
        legendreCubic (x16LegendreModulus α β) z := by
  have hroot : β * x16LegendreLambda α β = β - α := by
    unfold x16LegendreLambda
    field_simp [hβ]
  have hmod : x16LegendreLambda α β * x16LegendreModulus α β = 1 := by
    unfold x16LegendreLambda x16LegendreModulus
    field_simp [hβ, sub_ne_zero.mpr hsep]
  have hfactor (x : ℚ) :
      x16WeierstrassRhs t x = x * (x - α) * (x - β) := by
    unfold x16WeierstrassRhs
    calc
      x * (x ^ 2 + x16WeierstrassA t * x + t) =
          x * (x ^ 2 - (α + β) * x + α * β) := by rw [hA, ← ht]; ring
      _ = x * (x - α) * (x - β) := by ring
  rw [hfactor]
  exact weierstrass_root_cubic_to_legendre α β
    (x16LegendreLambda α β) (x16LegendreModulus α β) z
    hroot hmod hden

end OddZeta
