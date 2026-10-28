import OddZeta.MellinRationalMoments

namespace OddZeta

theorem involution_residue_sum_zero {ι : Type*} [Fintype ι]
    (e : ι ≃ ι) (c : ι → ℚ) (hc : ∀ i, c (e i) = -c i) : ∑ i, c i = 0 := by
  have h := Equiv.sum_comp e c
  simp_rw [hc] at h
  rw [Finset.sum_neg_distrib] at h
  linarith

def barnesFiveExample (t : ℚ) : ℚ :=
  let T := t * (t + 1)
  (-23 * T ^ 2 + 39 * T + 14) / T ^ 4

theorem barnesFiveExample_partial_fractions (t : ℚ) (ht : t ≠ 0) (ht1 : t + 1 ≠ 0) :
    barnesFiveExample t = -17 / t ^ 3 + 14 / t ^ 4 +
      17 / (t + 1) ^ 3 + 14 / (t + 1) ^ 4 := by
  unfold barnesFiveExample
  dsimp
  field_simp
  ring

def barnesFiveSummand (t : ℚ) : ℚ :=
  let T := t * (t + 1)
  (2 * t + 1) * (-46 * T ^ 2 + 117 * T + 56) / T ^ 5

theorem barnesFiveSummand_partial_fractions (t : ℚ) (ht : t ≠ 0) (ht1 : t + 1 ≠ 0) :
    barnesFiveSummand t = -51 / t ^ 4 + 56 / t ^ 5 +
      51 / (t + 1) ^ 4 + 56 / (t + 1) ^ 5 := by
  unfold barnesFiveSummand
  dsimp
  field_simp
  ring

noncomputable def barnesFiveExampleForm (n : ℕ) : ℝ :=
  -51 / ((n : ℝ) + 1) ^ 4 + 56 / ((n : ℝ) + 1) ^ 5 +
    51 / ((n : ℝ) + 2) ^ 4 + 56 / ((n : ℝ) + 2) ^ 5

theorem barnesFiveExample_hasSum :
    HasSum barnesFiveExampleForm (112 * mellinZetaValue 3 - 107) := by
  have h := (((mellin_zeta_hasSum 2).mul_left (-51)).add
    ((mellin_zeta_hasSum 3).mul_left 56)).add
      (((mellin_zeta_tail_hasSum 2 1).mul_left 51).add
        ((mellin_zeta_tail_hasSum 3 1).mul_left 56))
  have hv : -51 * mellinZetaValue 2 + 56 * mellinZetaValue 3 +
      (51 * (mellinZetaValue 2 - (harmonicPower 4 1 : ℝ)) +
        56 * (mellinZetaValue 3 - (harmonicPower 5 1 : ℝ))) =
        112 * mellinZetaValue 3 - 107 := by
    norm_num [harmonicPower]
    ring
  rw [← hv]
  apply h.congr_fun
  intro n
  simp only [barnesFiveExampleForm, Nat.cast_add, Nat.cast_one]
  ring

theorem barnesFiveSummand_hasSum :
    HasSum (fun n : ℕ => (barnesFiveSummand ((n + 1 : ℕ) : ℚ) : ℝ))
      (112 * mellinZetaValue 3 - 107) := by
  apply barnesFiveExample_hasSum.congr_fun
  intro n
  have h := barnesFiveSummand_partial_fractions ((n + 1 : ℕ) : ℚ)
    (by positivity) (by positivity)
  have hR := congrArg (fun q : ℚ => (q : ℝ)) h
  norm_num [barnesFiveExampleForm, add_assoc] at hR ⊢
  exact hR

theorem barnesFiveExample_lower : 5 ≤ 112 * mellinZetaValue 3 - 107 := by
  have hz := (mellin_zeta_hasSum 3).summable.le_tsum 0 (fun j _ => by positivity)
  rw [(mellin_zeta_hasSum 3).tsum_eq] at hz
  norm_num at hz
  linarith

theorem pade_lower_period_elimination {ι : Type*} [Fintype ι]
    (w A B C : ι → ℚ) (x y : ℝ) (hcancel : ∑ i, w i * A i = 0) :
    (∑ i, (w i : ℝ) * ((A i : ℝ) * x + (B i : ℝ) * y + (C i : ℝ))) =
      ((∑ i, w i * B i : ℚ) : ℝ) * y + ((∑ i, w i * C i : ℚ) : ℝ) := by
  have hc : (∑ i, (w i : ℝ) * (A i : ℝ)) = 0 := by exact_mod_cast hcancel
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hc, zero_mul, zero_add]
  push_cast
  rfl

theorem pade_coordinate_elimination {ι κ : Type*} [Fintype ι] [Fintype κ]
    (target : κ) (w : ι → ℚ) (A : ι → κ → ℚ) (B : ι → ℚ) (z : κ → ℝ)
    (hcancel : ∀ k ≠ target, ∑ i, w i * A i k = 0) :
    (∑ i, (w i : ℝ) * ((∑ k, (A i k : ℝ) * z k) + (B i : ℝ))) =
      ((∑ i, w i * A i target : ℚ) : ℝ) * z target +
        ((∑ i, w i * B i : ℚ) : ℝ) := by
  classical
  calc
    _ = (∑ k, ((∑ i, w i * A i k : ℚ) : ℝ) * z k) +
        ((∑ i, w i * B i : ℚ) : ℝ) := by
      simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      push_cast
      simp_rw [← mul_assoc, Finset.sum_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_eq_single target
      · intro k _ hk
        rw [hcancel k hk]
        simp
      · simp

end OddZeta
