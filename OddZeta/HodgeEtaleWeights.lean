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

/-- Hodge-circle character on the `i`th line in `Sym^d H^1(E)` for an
elliptic curve: the Hodge types contribute exponents `d - 2i`. -/
def ellipticSymmetricCircleExponent (d i : ℕ) : ℤ :=
  (d : ℤ) - 2 * (i : ℤ)

/-- Candidate symmetric-power degree associated to the odd weight `2r+1`. -/
def oddZetaEllipticDegree (r : ℕ) : ℕ := 2 * r

def oddZetaEllipticCircleExponent (r i : ℕ) : ℤ :=
  ellipticSymmetricCircleExponent (oddZetaEllipticDegree r) i

theorem oddZetaEllipticCircle_top (r : ℕ) :
    oddZetaEllipticCircleExponent r 0 = 2 * (r : ℤ) := by
  simp [oddZetaEllipticCircleExponent, ellipticSymmetricCircleExponent,
    oddZetaEllipticDegree]

theorem oddZetaEllipticCircle_bottom (r : ℕ) :
    oddZetaEllipticCircleExponent r (2 * r) = -2 * (r : ℤ) := by
  simp [oddZetaEllipticCircleExponent, ellipticSymmetricCircleExponent,
    oddZetaEllipticDegree]
  ring

/-- For each odd zeta weight at least three, its candidate elliptic symmetric
power has nontrivial Hodge-circle action. -/
theorem oddZeta_elliptic_circle_nontrivial {r : ℕ} (hr : 0 < r) :
    oddZetaEllipticCircleExponent r 0 ≠ 0 := by
  rw [oddZetaEllipticCircle_top]
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
  omega

/-- The middle line of an even symmetric power has trivial circle character. -/
theorem oddZeta_elliptic_circle_middle (r : ℕ) :
    oddZetaEllipticCircleExponent r r = 0 := by
  simp [oddZetaEllipticCircleExponent, ellipticSymmetricCircleExponent,
    oddZetaEllipticDegree]

/-- The residue line in `H^1(E \\ {O,P})` has Tate type `(1,1)` and hence
trivial Hodge-circle character. The open curve's elliptic graded part still
has nontrivial characters. -/
def affineEllipticResidueCircleExponent : ℤ := hodgeCircleExponent 1 1

theorem affineEllipticResidue_circle_trivial :
    affineEllipticResidueCircleExponent = 0 := by
  norm_num [affineEllipticResidueCircleExponent, hodgeCircleExponent]

/-- Associated-graded circle characters for the first cohomology of an
elliptic curve punctured at two marked points: the two elliptic characters
and the residue Tate character. -/
def affineEllipticH1AssociatedGradedCircleExponent (i : Fin 3) : ℤ :=
  if i.val = 0 then 1 else if i.val = 1 then -1 else
    affineEllipticResidueCircleExponent

theorem affineEllipticH1_circle_nontrivial :
    ∃ i : Fin 3,
      affineEllipticH1AssociatedGradedCircleExponent i ≠ 0 := by
  refine ⟨⟨0, by omega⟩, ?_⟩
  simp [affineEllipticH1AssociatedGradedCircleExponent]

end OddZeta
