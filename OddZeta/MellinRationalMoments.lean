import OddZeta.OddHankelArithmetic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.PSeries

namespace OddZeta

noncomputable def mellinResidue {n : ℕ} (e : Fin (n + 2) → ℚ) (i : Fin (n + 2)) : ℚ :=
  Lagrange.nodalWeight Finset.univ (fun j => -e j) i

theorem mellinResidue_sum_zero {n : ℕ} (e : Fin (n + 2) → ℚ)
    (he : Function.Injective e) : ∑ i, mellinResidue e i = 0 := by
  have hv : Set.InjOn (fun i => -e i) (Finset.univ : Finset (Fin (n + 2))) := by
    intro i _ j _ hij
    exact he (neg_injective hij)
  have h := Lagrange.coeff_eq_sum (P := (1 : Polynomial ℚ)) hv (by simp; positivity)
  simpa [mellinResidue, Lagrange.nodalWeight, Finset.prod_inv_distrib,
    one_div, Polynomial.coeff_one] using h.symm

theorem mellin_partial_fractions {n : ℕ} (e : Fin (n + 2) → ℚ)
    (he : Function.Injective e) (x : ℚ) (hx : ∀ i, x + e i ≠ 0) :
    ∑ i, mellinResidue e i / (x + e i) = (∏ i, (x + e i))⁻¹ := by
  have hv : Set.InjOn (fun i => -e i) (Finset.univ : Finset (Fin (n + 2))) := by
    intro i _ j _ hij
    exact he (neg_injective hij)
  have hx' : ∀ i ∈ (Finset.univ : Finset (Fin (n + 2))), x ≠ -e i := by
    intro i _ h
    apply hx i
    rw [h]
    ring
  have h := Lagrange.eval_interpolate_not_at_node
    (fun _ : Fin (n + 2) => (1 : ℚ)) hx'
  have hs : (Finset.univ : Finset (Fin (n + 2))).Nonempty := Finset.univ_nonempty
  change Polynomial.eval x (Lagrange.interpolate Finset.univ (fun j => -e j) 1) = _ at h
  rw [Lagrange.interpolate_one hv hs, Polynomial.eval_one] at h
  simp only [Lagrange.eval_nodal, sub_neg_eq_add, mul_one] at h
  have hp : (∏ i, (x + e i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  rw [← one_div]
  apply (eq_div_iff hp).mpr
  simpa [mellinResidue, div_eq_mul_inv, mul_comm] using h.symm

def mellinHarmonicTail (start length : ℕ) : ℚ :=
  ∑ k ∈ Finset.range length, 1 / ((start + k + 1 : ℕ) : ℚ)

theorem harmonicPower_one_succ (m : ℕ) :
    harmonicPower 1 (m + 1) = harmonicPower 1 m + 1 / ((m + 1 : ℕ) : ℚ) := by
  simp [harmonicPower, Finset.sum_range_succ]

theorem mellinHarmonicTail_eq (start length : ℕ) :
    mellinHarmonicTail start length =
      harmonicPower 1 (start + length) - harmonicPower 1 start := by
  induction length with
  | zero => simp [mellinHarmonicTail]
  | succ length ih =>
    simp only [mellinHarmonicTail, Finset.sum_range_succ] at ih ⊢
    rw [show start + (length + 1) = start + length + 1 by omega,
      harmonicPower_one_succ]
    linarith

theorem mellinHarmonicTail_bounds (start length : ℕ) :
    0 ≤ mellinHarmonicTail start length ∧
      mellinHarmonicTail start length ≤ (length : ℚ) / ((start + 1 : ℕ) : ℚ) := by
  constructor
  · unfold mellinHarmonicTail
    exact Finset.sum_nonneg (fun k _ => by positivity)
  · calc
      mellinHarmonicTail start length ≤
          ∑ _k ∈ Finset.range length, 1 / ((start + 1 : ℕ) : ℚ) := by
        apply Finset.sum_le_sum
        intro k _
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (show start + 1 ≤ start + k + 1 by omega)
      _ = (length : ℚ) / ((start + 1 : ℕ) : ℚ) := by simp; ring

noncomputable def mellinRationalMoment {n : ℕ} (e : Fin (n + 2) → ℕ) : ℚ :=
  -∑ i, mellinResidue (fun j => (e j : ℚ)) i * harmonicPower 1 (e i)

theorem mellin_finite_sum {n : ℕ} (e : Fin (n + 2) → ℕ)
    (he : Function.Injective e) (length : ℕ) :
    (∑ k ∈ Finset.range length, (∏ i, ((k + 1 + e i : ℕ) : ℚ))⁻¹) =
      ∑ i, mellinResidue (fun j => (e j : ℚ)) i *
        (harmonicPower 1 (length + e i) - harmonicPower 1 (e i)) := by
  have heQ : Function.Injective (fun i => (e i : ℚ)) := by
    intro i j hij
    change (e i : ℚ) = (e j : ℚ) at hij
    apply he
    exact_mod_cast hij
  calc
    _ = ∑ k ∈ Finset.range length,
        ∑ i, mellinResidue (fun j => (e j : ℚ)) i / ((k + 1 + e i : ℕ) : ℚ) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (mellin_partial_fractions (fun j => (e j : ℚ)) heQ (k + 1) (fun i => by positivity)).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      have ht := mellinHarmonicTail_eq (e i) length
      unfold mellinHarmonicTail at ht
      simpa only [div_eq_mul_inv, one_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using congrArg
          (fun z : ℚ => mellinResidue (fun j => (e j : ℚ)) i * z) ht

theorem mellin_remainder_identity {n : ℕ} (e : Fin (n + 2) → ℕ)
    (he : Function.Injective e) (length : ℕ) :
    (∑ k ∈ Finset.range length, (∏ i, ((k + 1 + e i : ℕ) : ℚ))⁻¹) -
        mellinRationalMoment e =
      ∑ i, mellinResidue (fun j => (e j : ℚ)) i * mellinHarmonicTail length (e i) := by
  rw [mellin_finite_sum e he]
  have heQ : Function.Injective (fun i => (e i : ℚ)) := by
    intro i j hij
    change (e i : ℚ) = (e j : ℚ) at hij
    apply he
    exact_mod_cast hij
  have hc := mellinResidue_sum_zero (fun j => (e j : ℚ)) heQ
  simp only [mellinRationalMoment, mellinHarmonicTail_eq]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hc]
  ring

noncomputable def mellinRemainderConstant {n : ℕ} (e : Fin (n + 2) → ℕ) : ℚ :=
  ∑ i, |mellinResidue (fun j => (e j : ℚ)) i| * (e i : ℚ)

theorem mellin_finite_sum_error {n : ℕ} (e : Fin (n + 2) → ℕ)
    (he : Function.Injective e) (length : ℕ) :
    |(∑ k ∈ Finset.range length, (∏ i, ((k + 1 + e i : ℕ) : ℚ))⁻¹) -
        mellinRationalMoment e| ≤ mellinRemainderConstant e / ((length + 1 : ℕ) : ℚ) := by
  rw [mellin_remainder_identity e he]
  calc
    _ ≤ ∑ i, |mellinResidue (fun j => (e j : ℚ)) i * mellinHarmonicTail length (e i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |mellinResidue (fun j => (e j : ℚ)) i| * mellinHarmonicTail length (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (mellinHarmonicTail_bounds length (e i)).1]
    _ ≤ ∑ i, |mellinResidue (fun j => (e j : ℚ)) i| *
        ((e i : ℚ) / ((length + 1 : ℕ) : ℚ)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (mellinHarmonicTail_bounds length (e i)).2 (abs_nonneg _)
    _ = _ := by simp only [mellinRemainderConstant, mul_div_assoc, Finset.sum_div]

theorem mellin_series_limit {n : ℕ} (e : Fin (n + 2) → ℕ)
    (he : Function.Injective e) :
    Filter.Tendsto (fun length =>
      ((∑ k ∈ Finset.range length, (∏ i, ((k + 1 + e i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ))
      Filter.atTop (nhds (mellinRationalMoment e : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound (length : ℕ) :
      ‖((∑ k ∈ Finset.range length, (∏ i, ((k + 1 + e i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ) -
        (mellinRationalMoment e : ℝ)‖ ≤
      (mellinRemainderConstant e : ℝ) / ((length : ℝ) + 1) := by
    rw [Real.norm_eq_abs]
    exact_mod_cast mellin_finite_sum_error e he length
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa only [mul_zero, mul_one_div] using h.const_mul (mellinRemainderConstant e : ℝ)

theorem mellin_rational_hasSum {n : ℕ} (e : Fin (n + 2) → ℕ)
    (he : Function.Injective e) :
    HasSum (fun k => (((∏ i, ((k + 1 + e i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ))
      (mellinRationalMoment e : ℝ) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity) _).mpr
  simpa only [Rat.cast_sum] using mellin_series_limit e he

noncomputable def mellinZetaValue (n : ℕ) : ℝ :=
  (riemannZeta ((n + 2 : ℕ) : ℂ)).re

theorem mellinZetaValue_eq_tsum (n : ℕ) :
    mellinZetaValue n = ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (n + 2) := by
  have hs : 1 < (((n + 2 : ℕ) : ℂ)).re := by
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hz : riemannZeta ((n + 2 : ℕ) : ℂ) =
      ((∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (n + 2) : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.ofReal_tsum]
    apply tsum_congr
    intro k
    simp only [Complex.cpow_natCast]
    push_cast
    rfl
  simpa [mellinZetaValue] using congrArg Complex.re hz

theorem mellin_zeta_hasSum (n : ℕ) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (n + 2)) (mellinZetaValue n) := by
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ) ^ (n + 2)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hs' := (summable_nat_add_iff 1).mpr hs
  simpa only [Nat.cast_add, Nat.cast_one, ← mellinZetaValue_eq_tsum] using hs'.hasSum

theorem mellin_zeta_tail_hasSum (n shift : ℕ) :
    HasSum (fun k : ℕ => 1 / (((k + shift : ℕ) : ℝ) + 1) ^ (n + 2))
      (mellinZetaValue n - (harmonicPower (n + 2) shift : ℝ)) := by
  rw [hasSum_nat_add_iff shift (f := fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (n + 2))]
  have hh : (harmonicPower (n + 2) shift : ℝ) =
      ∑ k ∈ Finset.range shift, 1 / ((k : ℝ) + 1) ^ (n + 2) := by
    simp [harmonicPower]
  rw [← hh, sub_add_cancel]
  exact mellin_zeta_hasSum n

def toricMellinExponent (n j k : ℕ) (i : Fin (n + 2)) : ℕ :=
  i.val * j + (n + 1 - i.val) * k

theorem toricMellin_sum (n j k j' k' : ℕ) (i : Fin (n + 2)) :
    toricMellinExponent n j k i + toricMellinExponent n j' k' i =
      toricMellinExponent n (j + j') (k + k') i := by
  unfold toricMellinExponent
  ring

theorem toricMellin_diagonal (n j : ℕ) (i : Fin (n + 2)) :
    toricMellinExponent n j j i = (n + 1) * j := by
  have hi : i.val ≤ n + 1 := by have h := i.isLt; omega
  unfold toricMellinExponent
  rw [← add_mul, Nat.add_sub_of_le hi]

theorem toricMellin_distinct (n j k : ℕ) (hjk : j ≠ k) :
    Function.Injective (toricMellinExponent n j k) := by
  intro i l h
  have hi : i.val ≤ n + 1 := by have h := i.isLt; omega
  have hl : l.val ≤ n + 1 := by have h := l.isLt; omega
  have hZ := congrArg (fun z : ℕ => (z : ℤ)) h
  simp only [toricMellinExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hi,
    Nat.cast_sub hl, Nat.cast_one] at hZ
  have hp : ((i.val : ℤ) - l.val) * ((j : ℤ) - k) = 0 := by nlinarith
  have hne : (j : ℤ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjk)
  have hval := (mul_eq_zero.mp hp).resolve_right hne
  apply Fin.ext
  exact_mod_cast (sub_eq_zero.mp hval)

theorem toricMellin_rational_hasSum (n j k : ℕ) (hjk : j ≠ k) :
    HasSum (fun q =>
      (((∏ i, ((q + 1 + toricMellinExponent n j k i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ))
      (mellinRationalMoment (toricMellinExponent n j k) : ℝ) :=
  mellin_rational_hasSum _ (toricMellin_distinct n j k hjk)

theorem toricMellin_diagonal_hasSum (n j : ℕ) :
    HasSum (fun q =>
      (((∏ i, ((q + 1 + toricMellinExponent n j j i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ))
      (mellinZetaValue n - (harmonicPower (n + 2) ((n + 1) * j) : ℝ)) := by
  convert! mellin_zeta_tail_hasSum n ((n + 1) * j) using 1
  funext q
  simp only [toricMellin_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Rat.cast_inv, Rat.cast_pow, Nat.cast_add, Nat.cast_one, one_div]
  congr 2
  push_cast
  ring

noncomputable def toricMellinPeriod (n j k : ℕ) : ℝ :=
  if j = k then mellinZetaValue n - (harmonicPower (n + 2) ((n + 1) * j) : ℝ)
  else (mellinRationalMoment (toricMellinExponent n j k) : ℝ)

theorem toricMellin_period_hasSum (n j k : ℕ) :
    HasSum (fun q =>
      (((∏ i, ((q + 1 + toricMellinExponent n j k i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ))
      (toricMellinPeriod n j k) := by
  by_cases h : j = k
  · subst k
    simpa [toricMellinPeriod] using toricMellin_diagonal_hasSum n j
  · simpa only [toricMellinPeriod, ite_eq_right h] using toricMellin_rational_hasSum n j k h

theorem toricMellin_exponent_shift (n j k : ℕ) (i : Fin (n + 2)) :
    toricMellinExponent n (j + 1) (k + 1) i = toricMellinExponent n j k i + (n + 1) := by
  have hi : i.val ≤ n + 1 := by have h := i.isLt; omega
  unfold toricMellinExponent
  calc
    i.val * (j + 1) + (n + 1 - i.val) * (k + 1) =
        i.val * j + (n + 1 - i.val) * k + (i.val + (n + 1 - i.val)) := by ring
    _ = _ := by rw [Nat.add_sub_of_le hi]

theorem toricMellin_contiguity (n j k : ℕ) :
    toricMellinPeriod n (j + 1) (k + 1) = toricMellinPeriod n j k -
      ∑ q ∈ Finset.range (n + 1),
        (((∏ i, ((q + 1 + toricMellinExponent n j k i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ) := by
  have hs : HasSum (fun q =>
      (((∏ i, ((q + (n + 1) + 1 + toricMellinExponent n j k i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ))
      (toricMellinPeriod n (j + 1) (k + 1)) := by
    simpa only [toricMellin_exponent_shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using toricMellin_period_hasSum n (j + 1) (k + 1)
  have hs' := (hasSum_nat_add_iff (n + 1)
    (f := fun q =>
      (((∏ i, ((q + 1 + toricMellinExponent n j k i : ℕ) : ℚ))⁻¹ : ℚ) : ℝ))).mp hs
  have h := (toricMellin_period_hasSum n j k).unique hs'
  linarith

theorem toric_pole_identity {R : Type*} [CommRing R] (n : ℕ) (T : R) :
    T ^ (n + 1) - 1 = (T - 1) * (∑ k ∈ Finset.range (n + 1), T ^ k) := by
  rw [mul_comm, geom_sum_mul]

theorem toric_pole_cancellation {F : Type*} [Field F] (n : ℕ) (T : F) (hT : T ≠ 1) :
    (T ^ (n + 1) - 1) / (1 - T) = -(∑ k ∈ Finset.range (n + 1), T ^ k) := by
  apply (div_eq_iff (sub_ne_zero.mpr hT.symm)).mpr
  rw [toric_pole_identity]
  ring

def balancedMellinExponent (r K t : ℕ) (u : ℤ) (i : Fin (2 * r + 1)) : ℤ :=
  (K : ℤ) + t + ((i.val : ℤ) - r) * u

theorem balancedMellin_sum (r K t t' : ℕ) (u v : ℤ) (i : Fin (2 * r + 1)) :
    balancedMellinExponent r K t u i + balancedMellinExponent r K t' v i =
      2 * (K : ℤ) + t + t' + ((i.val : ℤ) - r) * (u + v) := by
  unfold balancedMellinExponent
  ring

theorem balancedMellin_collision {r K t t' : ℕ} (u v : ℤ) (h : u + v = 0)
    (i : Fin (2 * r + 1)) :
    balancedMellinExponent r K t u i + balancedMellinExponent r K t' v i =
      2 * (K : ℤ) + t + t' := by
  rw [balancedMellin_sum, h, mul_zero, add_zero]

theorem balancedMellin_distinct {r K t t' : ℕ} (u v : ℤ) (h : u + v ≠ 0) :
    Function.Injective (fun i : Fin (2 * r + 1) =>
      balancedMellinExponent r K t u i + balancedMellinExponent r K t' v i) := by
  intro i j hij
  change balancedMellinExponent r K t u i + balancedMellinExponent r K t' v i =
    balancedMellinExponent r K t u j + balancedMellinExponent r K t' v j at hij
  rw [balancedMellin_sum, balancedMellin_sum] at hij
  have hc : ((i.val : ℤ) - r) * (u + v) = ((j.val : ℤ) - r) * (u + v) := by omega
  have hv := mul_right_cancel₀ h hc
  apply Fin.ext
  exact_mod_cast (show (i.val : ℤ) = (j.val : ℤ) by omega)

end OddZeta
