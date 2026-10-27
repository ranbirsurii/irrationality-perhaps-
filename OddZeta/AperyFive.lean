import Mathlib

/-!
# The first deformed Apéry coefficient

This file formalizes the rational coefficient data stated in the supplied
`r = 2` calculation. In particular, it defines the Apéry coefficients and
the displayed harmonic-number expression for `C n`, and proves the stated
`n = 1` values and scalar elimination identity.

The source text asserts that partial fractions of the infinite series give
these coefficients; that analytic derivation is not part of these finite
rational identities. The Adams projector below is likewise only its scalar
eigenvalue calculation. No regulator class or motivic lift is constructed.
-/

namespace OddZeta

/-- The numerator in the rational Apéry function `F_n(t)`. -/
def aperyNumerator (n : ℕ) (t : ℚ) : ℚ :=
  ∏ j ∈ Finset.range n, (t - (j + 1 : ℚ))

/-- The denominator in the rational Apéry function `F_n(t)`. -/
def aperyDenominator (n : ℕ) (t : ℚ) : ℚ :=
  ∏ j ∈ Finset.range (n + 1), (t + (j : ℚ))

/-- The squared rational function `F_n(t)` used in the supplied deformation. -/
def aperyF (n : ℕ) (t : ℚ) : ℚ :=
  (aperyNumerator n t / aperyDenominator n t) ^ 2

/-- The finite deformation kernel `R_n(t,z)` from the chat text. -/
def aperyR (n : ℕ) (t z : ℚ) : ℚ :=
  aperyF n t * ∏ j ∈ Finset.range (n + 1),
    (1 + z / (t + (j : ℚ)) ^ 2)⁻¹

/-- Each integer zero of the numerator remains a zero of the deformed kernel. -/
theorem aperyR_zero_at_integer (n i : ℕ) (hi : i < n) (z : ℚ) :
    aperyR n (i + 1 : ℚ) z = 0 := by
  have hnum : aperyNumerator n (i + 1 : ℚ) = 0 := by
    unfold aperyNumerator
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    simp
  simp [aperyR, aperyF, hnum]

/-- The rational harmonic number `H_n`. -/
def harmonic (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (j + 1 : ℚ)⁻¹

/-- The rational second-order harmonic number `H_n^(2)`. -/
def harmonicTwo (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (j + 1 : ℚ)⁻¹ ^ 2

/-- The rational Apéry summand `binom(n,k)^2 binom(n+k,k)^2`. -/
def aperySummand (n k : ℕ) : ℚ :=
  ((Nat.choose n k : ℚ) ^ 2) * ((Nat.choose (n + k) k : ℚ) ^ 2)

/-- The Apéry denominator coefficient `A_n`. -/
def aperyA (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), aperySummand n k

/-- The harmonic combination `eta_(n,k)` from the source calculation. -/
def aperyEta (n k : ℕ) : ℚ :=
  harmonic (n + k) + harmonic (n - k) - 2 * harmonic k

/-- The explicitly stated coefficient of `zeta(3)` in `L_(n,1)`. -/
def aperyC (n : ℕ) : ℚ :=
  -2 * ∑ k ∈ Finset.range (n + 1),
    aperySummand n k *
      (2 * aperyEta n k ^ 2 - harmonicTwo (n + k) +
        3 * harmonicTwo k + 2 * harmonicTwo (n - k))

theorem aperyA_one : aperyA 1 = 5 := by
  norm_num [aperyA, aperySummand, Finset.sum_range_succ]

theorem aperyC_one : aperyC 1 = -36 := by
  norm_num [aperyC, aperySummand, aperyEta, harmonic, harmonicTwo,
    Finset.sum_range_succ]

/-- The two stated coefficient formulas, with their rational terms exposed. -/
def aperyL0 (n : ℕ) (zeta3 : ℝ) (b : ℚ) : ℝ :=
  2 * (aperyA n : ℝ) * zeta3 - (b : ℝ)

def aperyL1 (n : ℕ) (zeta3 zeta5 : ℝ) (E : ℚ) : ℝ :=
  -4 * (aperyA n : ℝ) * zeta5 + (aperyC n : ℝ) * zeta3 + (E : ℝ)

/-- Scalar elimination cancels the `zeta(3)` term exactly. -/
theorem apery_scalar_elimination
    (n : ℕ) (zeta3 zeta5 : ℝ) (b E : ℚ) :
    2 * (aperyA n : ℝ) * aperyL1 n zeta3 zeta5 E -
        (aperyC n : ℝ) * aperyL0 n zeta3 b =
      -8 * (aperyA n : ℝ) ^ 2 * zeta5 +
        ((2 * aperyA n * E + aperyC n * b : ℚ) : ℝ) := by
  unfold aperyL0 aperyL1
  push_cast
  ring

/-- The `n = 1` first-level forms recorded in the source. -/
theorem apery_L0_one (zeta3 : ℝ) :
    aperyL0 1 zeta3 (12 : ℚ) = 10 * zeta3 - 12 := by
  unfold aperyL0
  rw [aperyA_one]
  norm_num

theorem apery_L1_one (zeta3 zeta5 : ℝ) :
    aperyL1 1 zeta3 zeta5 (64 : ℚ) = -20 * zeta5 - 36 * zeta3 + 64 := by
  unfold aperyL1
  rw [aperyA_one, aperyC_one]
  norm_num
  ring

/-- The displayed `n = 1` scalar elimination check. -/
theorem apery_elimination_one (zeta3 zeta5 : ℝ) :
    10 * (-20 * zeta5 - 36 * zeta3 + 64) +
        36 * (10 * zeta3 - 12) = -200 * zeta5 + 208 := by
  ring

/-- The scalar polynomial corresponding to `(psi_2 - 8 I) / 24`. -/
def adamsProjector5Eigenvalue (eigenvalue : ℚ) : ℚ :=
  (eigenvalue - 8) / 24

/-- Apply `(psi_2 - 8 I) / 24` to a vector in a rational vector space. -/
def adamsProjector5Apply {V : Type} [AddCommGroup V] [Module ℚ V]
    (psi : V →ₗ[ℚ] V) (v : V) : V :=
  (1 / 24 : ℚ) • (psi v - (8 : ℚ) • v)

theorem adamsProjector5Apply_kills_weight3 {V : Type}
    [AddCommGroup V] [Module ℚ V] (psi : V →ₗ[ℚ] V) (v : V)
    (hpsi : psi v = (8 : ℚ) • v) :
    adamsProjector5Apply psi v = 0 := by
  simp [adamsProjector5Apply, hpsi]

theorem adamsProjector5Apply_fixes_weight5 {V : Type}
    [AddCommGroup V] [Module ℚ V] (psi : V →ₗ[ℚ] V) (v : V)
    (hpsi : psi v = (32 : ℚ) • v) :
    adamsProjector5Apply psi v = v := by
  unfold adamsProjector5Apply
  rw [hpsi]
  have h : (32 : ℚ) • v - (8 : ℚ) • v = (24 : ℚ) • v := by
    module
  rw [h]
  simp [smul_smul]

theorem adamsProjector5_kills_weight3 :
    adamsProjector5Eigenvalue 8 = 0 := by
  norm_num [adamsProjector5Eigenvalue]

theorem adamsProjector5_fixes_weight5 :
    adamsProjector5Eigenvalue 32 = 1 := by
  norm_num [adamsProjector5Eigenvalue]

theorem adamsProjector5_scales_weight0_rational_part :
    adamsProjector5Eigenvalue 1 = -(7 : ℚ) / 24 := by
  norm_num [adamsProjector5Eigenvalue]

end OddZeta
