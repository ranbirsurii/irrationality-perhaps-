import Mathlib

/-!
# Hodge-circle and étale weight bookkeeping

These definitions record the realizations a Tate-graded class would have.
They do not construct a class from the deformed Apéry family. In particular,
the circle action alone does not separate Tate twists; the weight cocharacter
and the étale cyclotomic character carry the twist index.
-/

namespace OddZeta

/-- The character exponent of the Hodge circle on a Hodge type `(p,q)`. -/
def hodgeCircleExponent (p q : ℤ) : ℤ := p - q

/-- The weight-cocharacter exponent on a Hodge type `(p,q)`. -/
def hodgeWeightExponent (p q : ℤ) : ℤ := p + q

/-- A Tate twist `Q(m)` has Hodge type `(-m,-m)`, étale cyclotomic exponent
`m`, and Adams weight `m`. -/
structure TateRealizationData where
  hodgeP : ℤ
  hodgeQ : ℤ
  etaleCyclotomicExponent : ℕ
  adamsWeight : ℕ
  deriving DecidableEq, Repr

def tateRealizationData (m : ℕ) : TateRealizationData where
  hodgeP := -(m : ℤ)
  hodgeQ := -(m : ℤ)
  etaleCyclotomicExponent := m
  adamsWeight := m

theorem tate_hodge_circle_trivial (m : ℕ) :
    hodgeCircleExponent (tateRealizationData m).hodgeP
      (tateRealizationData m).hodgeQ = 0 := by
  simp [hodgeCircleExponent, tateRealizationData]

theorem tate_weight_cocharacter_exponent (m : ℕ) :
    hodgeWeightExponent (tateRealizationData m).hodgeP
      (tateRealizationData m).hodgeQ = -2 * (m : ℤ) := by
  simp [hodgeWeightExponent, tateRealizationData]
  ring

theorem tate_etale_cyclotomic_exponent (m : ℕ) :
    (tateRealizationData m).etaleCyclotomicExponent = m := rfl

theorem tate_adams_weight (m : ℕ) :
    (tateRealizationData m).adamsWeight = m := rfl

/-- On a Tate graded piece of Adams weight `m`, the `k`th Adams eigenvalue is
`k^m`; at `k = 2` this is the eigenvalue used by the projector. -/
def tateAdamsEigenvalue (k : ℚ) (m : ℕ) : ℚ := k ^ m

theorem tate_psi_two_eigenvalue (m : ℕ) :
    tateAdamsEigenvalue 2 m = 2 ^ m := rfl

/-- The Hodge-circle action cannot by itself distinguish Tate twists: all
Tate types `(−m,−m)` have circle exponent zero. -/
theorem hodge_circle_does_not_separate_tate_twists (m₁ m₂ : ℕ) :
    hodgeCircleExponent (-(m₁ : ℤ)) (-(m₁ : ℤ)) =
      hodgeCircleExponent (-(m₂ : ℤ)) (-(m₂ : ℤ)) := by
  simp [hodgeCircleExponent]

/-- The full weight cocharacter does separate distinct Tate twists. -/
theorem hodge_weight_separates_tate_twists {m₁ m₂ : ℕ}
    (h : hodgeWeightExponent (-(m₁ : ℤ)) (-(m₁ : ℤ)) =
      hodgeWeightExponent (-(m₂ : ℤ)) (-(m₂ : ℤ))) : m₁ = m₂ := by
  have h' : -2 * (m₁ : ℤ) = -2 * (m₂ : ℤ) := by
    dsimp [hodgeWeightExponent] at h
    nlinarith
  have hcast : (m₁ : ℤ) = (m₂ : ℤ) :=
    mul_left_cancel₀ (by norm_num : (-2 : ℤ) ≠ 0) h'
  exact_mod_cast hcast

/-- The `r`th odd-zeta weight corresponds to the Tate twist `2r+1`.
This is just the grading dictionary, not a construction of the motivic class.
-/
theorem odd_zeta_tate_adams_weight (r : ℕ) :
    (tateRealizationData (2 * r + 1)).adamsWeight = 2 * r + 1 := rfl

end OddZeta
