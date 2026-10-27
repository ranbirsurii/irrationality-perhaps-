import Mathlib
import OddZeta.AperyStructure

/-!
# Arithmetic checks for the Apéry K3 normal-function model

The Apéry K3 regulator construction gives an explicit inhomogeneous
Picard--Fuchs operator and a positive first forcing coefficient. This file
formalizes its exact rational coefficient data and finite positivity estimate.
It does not identify that K3 normal function with the separate deformed
`R_n(t,z)` family or with an odd-zeta irrationality form.
-/

namespace OddZeta

open Filter

def aperyK3PFThird (t : ℚ) : ℚ := t ^ 2 - 34 * t + 1

def aperyK3PFSecond (t : ℚ) : ℚ := 2 * t * (t - 17)

def aperyK3PFFirst (t : ℚ) : ℚ := 3 * t * (t - 9)

def aperyK3PFConstant (t : ℚ) : ℚ := t * (t - 5)

theorem aperyK3PFThird_eq_aperyDelta (t : ℚ) :
    aperyK3PFThird t = aperyDelta t := by
  rfl

/-- The rational summand in the first inhomogeneous coefficient
`10 + 5 * sum_{n >= 1} binom(2n,n)^2 / (16^n n (2n+2))`. -/
def aperyK3ForcingSummand (n : ℕ) : ℚ :=
  ((Nat.choose (2 * n) n : ℚ) ^ 2) /
    ((16 : ℚ) ^ n * (n : ℚ) * ((2 * n + 2 : ℕ) : ℚ))

/-- The first `N` terms of the Apéry K3 forcing coefficient. -/
def aperyK3ForcingPartial (N : ℕ) : ℚ :=
  10 + 5 * ∑ j ∈ Finset.range N, aperyK3ForcingSummand (j + 1)

def aperyK3TelescopingTerm (n : ℕ) : ℚ :=
  (1 : ℚ) / n - 1 / (n + 1)

theorem aperyK3ForcingSummand_nonneg (n : ℕ) :
    0 ≤ aperyK3ForcingSummand n := by
  unfold aperyK3ForcingSummand
  positivity

/-- A central binomial coefficient is bounded by the sum of all coefficients
in the next row of the binomial expansion. -/
theorem centralBinomial_le_four_pow (n : ℕ) :
    Nat.choose (2 * n) n ≤ 4 ^ n := by
  calc
    Nat.choose (2 * n) n ≤ Nat.choose (2 * n + 1) n := by
      apply Nat.choose_le_succ
    _ ≤ 4 ^ n := Nat.choose_middle_le_pow n

/-- The summand is dominated by a telescoping rational sequence. -/
theorem aperyK3ForcingSummand_le_telescoping (n : ℕ) (hn : 0 < n) :
    aperyK3ForcingSummand n ≤ aperyK3TelescopingTerm n := by
  have hchoose := centralBinomial_le_four_pow n
  have hchooseQ : (Nat.choose (2 * n) n : ℚ) ≤ 4 ^ n := by exact_mod_cast hchoose
  have hpow : (0 : ℚ) < 16 ^ n := by positivity
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hn1Q : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
  have hden : (0 : ℚ) < (16 : ℚ) ^ n * (n : ℚ) * ((2 * n + 2 : ℕ) : ℚ) := by
    positivity
  have hnum : (Nat.choose (2 * n) n : ℚ) ^ 2 ≤ 16 ^ n := by
    calc
      (Nat.choose (2 * n) n : ℚ) ^ 2 ≤ (4 ^ n) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hchooseQ 2
      _ = 16 ^ n := by
        calc
          ((4 : ℚ) ^ n) ^ 2 = (4 : ℚ) ^ (n * 2) := by rw [← pow_mul]
          _ = (4 : ℚ) ^ (2 * n) := by congr 1; omega
          _ = ((4 : ℚ) ^ 2) ^ n := by rw [pow_mul]
          _ = (16 : ℚ) ^ n := by norm_num
  unfold aperyK3ForcingSummand
  have hbound :
      ((Nat.choose (2 * n) n : ℚ) ^ 2) /
          ((16 : ℚ) ^ n * (n : ℚ) * ((2 * n + 2 : ℕ) : ℚ)) ≤
        (16 ^ n) / ((16 : ℚ) ^ n * (n : ℚ) * ((2 * n + 2 : ℕ) : ℚ)) :=
    (div_le_div_of_nonneg_right hnum (le_of_lt hden))
  have hden_simp : ((2 * n + 2 : ℕ) : ℚ) = 2 * ((n + 1 : ℕ) : ℚ) := by
    norm_num; ring
  rw [hden_simp] at hbound
  have hdiv :
      (16 : ℚ) ^ n / ((16 : ℚ) ^ n * (n : ℚ) *
          (2 * ((n + 1 : ℕ) : ℚ))) =
        1 / ((n : ℚ) * (2 * ((n + 1 : ℕ) : ℚ))) := by
    field_simp
  rw [hdiv] at hbound
  have htel :
      1 / ((n : ℚ) * (2 * ((n + 1 : ℕ) : ℚ))) ≤
        aperyK3TelescopingTerm n := by
    change 1 / ((n : ℚ) * (2 * ((n + 1 : ℕ) : ℚ))) ≤
      (1 : ℚ) / n - 1 / (n + 1)
    have hident : (1 : ℚ) / n - 1 / (n + 1) =
        1 / ((n : ℚ) * ((n + 1 : ℕ) : ℚ)) := by
      field_simp
      push_cast
      ring
    rw [hident]
    have hprod : (0 : ℚ) < (n : ℚ) * ((n + 1 : ℕ) : ℚ) := mul_pos hnQ hn1Q
    have htwo : (2 : ℚ) ≥ 1 := by norm_num
    rw [show (n : ℚ) * (2 * ((n + 1 : ℕ) : ℚ)) =
        2 * ((n : ℚ) * ((n + 1 : ℕ) : ℚ)) by ring]
    have hfrac :
        1 / (2 * ((n : ℚ) * ((n + 1 : ℕ) : ℚ))) ≤
          1 / ((n : ℚ) * ((n + 1 : ℕ) : ℚ)) := by
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hprod) hprod).2
      nlinarith [hprod]
    exact hfrac
  rw [hden_simp]
  exact hbound.trans htel

theorem aperyK3ForcingPartial_ge_ten (N : ℕ) :
    10 ≤ aperyK3ForcingPartial N := by
  unfold aperyK3ForcingPartial
  have hsum :
      0 ≤ ∑ j ∈ Finset.range N, aperyK3ForcingSummand (j + 1) := by
    apply Finset.sum_nonneg
    intro j hj
    exact aperyK3ForcingSummand_nonneg (j + 1)
  linarith

theorem aperyK3ForcingPartial_pos (N : ℕ) :
    0 < aperyK3ForcingPartial N := by
  have h := aperyK3ForcingPartial_ge_ten N
  linarith

theorem aperyK3Telescoping_sum (N : ℕ) :
    (∑ j ∈ Finset.range N, aperyK3TelescopingTerm (j + 1)) =
      1 - 1 / (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [aperyK3TelescopingTerm]
      push_cast
      field_simp
      ring

theorem aperyK3ForcingPartial_le_fifteen (N : ℕ) :
    aperyK3ForcingPartial N ≤ 15 := by
  have hsum :
      (∑ j ∈ Finset.range N, aperyK3ForcingSummand (j + 1)) ≤
        ∑ j ∈ Finset.range N, aperyK3TelescopingTerm (j + 1) := by
    apply Finset.sum_le_sum
    intro j hj
    exact aperyK3ForcingSummand_le_telescoping (j + 1) (by omega)
  rw [aperyK3Telescoping_sum] at hsum
  unfold aperyK3ForcingPartial
  have htail : 0 ≤ (1 : ℚ) / (N + 1) := by positivity
  linarith

theorem aperyK3ForcingPartial_mono {N M : ℕ} (hNM : N ≤ M) :
    aperyK3ForcingPartial N ≤ aperyK3ForcingPartial M := by
  have hsum :
      (∑ j ∈ Finset.range N, aperyK3ForcingSummand (j + 1)) ≤
        ∑ j ∈ Finset.range M, aperyK3ForcingSummand (j + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
    intro j hj hjnot
    exact aperyK3ForcingSummand_nonneg (j + 1)
  unfold aperyK3ForcingPartial
  nlinarith

def aperyK3ForcingPartialReal (N : ℕ) : ℝ :=
  aperyK3ForcingPartial N

/-- The finite forcing sums converge in the real numbers: their rational terms
are positive, and the central-binomial estimate bounds every partial sum. -/
theorem aperyK3ForcingPartialReal_converges :
    Tendsto aperyK3ForcingPartialReal atTop
      (nhds (sSup (Set.range aperyK3ForcingPartialReal))) := by
  have hm : Monotone aperyK3ForcingPartialReal := by
    intro a b hab
    change (aperyK3ForcingPartial a : ℝ) ≤ aperyK3ForcingPartial b
    exact_mod_cast aperyK3ForcingPartial_mono hab
  have hb : BddAbove (Set.range aperyK3ForcingPartialReal) := by
    refine ⟨15, ?_⟩
    rintro x ⟨N, rfl⟩
    change (aperyK3ForcingPartial N : ℝ) ≤ 15
    exact_mod_cast aperyK3ForcingPartial_le_fifteen N
  simpa [iSup] using tendsto_atTop_ciSup hm hb

end OddZeta
