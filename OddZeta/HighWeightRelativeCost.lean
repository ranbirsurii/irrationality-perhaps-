import OddZeta.IrrationalityCriterion

open Filter

namespace OddZeta

noncomputable def highWeightDecay (s : ℕ) : ℝ :=
  Real.log 140 + ((s : ℝ) - 5) * Real.log 4

theorem log_two_gt_two_thirds : (2 : ℝ) / 3 < Real.log 2 := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
  norm_num only [mul_one, show (1 : ℝ) + 2 = 3 by norm_num,
    show (1 : ℝ) + 1 = 2 by norm_num] at h
  exact h

theorem highWeightDecay_gap (s : ℕ) (hs : 7 ≤ s) :
    (s : ℝ) + 1 / 3 < highWeightDecay s := by
  have htwo := log_two_gt_two_thirds
  have h140 : (7 : ℝ) * Real.log 2 < Real.log 140 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 7)
      (by norm_num : (2 : ℝ) ^ 7 < 140)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have hsR : (7 : ℝ) ≤ s := by exact_mod_cast hs
  have hmul : ((s : ℝ) - 5) * (4 / 3) <
      ((s : ℝ) - 5) * Real.log 4 := by
    rw [hfour]
    exact mul_lt_mul_of_pos_left (by linarith) (by linarith)
  unfold highWeightDecay
  nlinarith

theorem smallness_of_eventual_relative_cost
    (s : ℕ) (hs : 7 ≤ s) (index : ℕ → ℕ)
    (hindex : Tendsto index atTop atTop)
    (D W S L : ℕ → ℝ)
    (hD : ∀ n, 0 ≤ D n) (hW : ∀ n, 0 ≤ W n)
    (hbound : ∀ᶠ n in atTop, |L n| ≤ D n * W n * S n)
    (hden : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      D n ≤ Real.exp (((s : ℝ) + ε) * (index n : ℝ)))
    (hcost : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      W n ≤ Real.exp (ε * (index n : ℝ)))
    (hraw : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      S n ≤ Real.exp ((-highWeightDecay s + ε) * (index n : ℝ))) :
    Tendsto L atTop (nhds 0) := by
  have hrate := highWeightDecay_gap s hs
  have hmajor : ∀ᶠ n in atTop,
      |L n| ≤ Real.exp (-(1 / 12 : ℝ) * (index n : ℝ)) := by
    filter_upwards [hbound, hden (1 / 12) (by norm_num),
      hcost (1 / 12) (by norm_num), hraw (1 / 12) (by norm_num)]
      with n hb hd hw hr
    have hprod : D n * W n ≤
        Real.exp (((s : ℝ) + 1 / 12) * (index n : ℝ)) *
        Real.exp ((1 / 12 : ℝ) * (index n : ℝ)) :=
      mul_le_mul hd hw (hW n) (Real.exp_pos _).le
    calc
      |L n| ≤ D n * W n * S n := hb
      _ ≤ D n * W n *
          Real.exp ((-highWeightDecay s + 1 / 12) * (index n : ℝ)) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg (hD n) (hW n))
      _ ≤ (Real.exp (((s : ℝ) + 1 / 12) * (index n : ℝ)) *
          Real.exp ((1 / 12 : ℝ) * (index n : ℝ))) *
          Real.exp ((-highWeightDecay s + 1 / 12) * (index n : ℝ)) :=
        mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ = Real.exp ((((s : ℝ) - highWeightDecay s) + 1 / 4) *
          (index n : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(1 / 12 : ℝ) * (index n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        linarith
  have harg : Tendsto (fun n => (1 / 12 : ℝ) * (index n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num)
      (tendsto_natCast_atTop_atTop.comp hindex)
  have hlim : Tendsto (fun n => Real.exp (-(1 / 12 : ℝ) * (index n : ℝ)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp harg
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 hmajor
  refine ⟨max N M, ?_⟩
  intro n hn
  have hexp := hN n (le_trans (le_max_left _ _) hn)
  have hb := hM n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, sub_zero] at hexp ⊢
  exact lt_of_le_of_lt hb (lt_of_le_of_lt (le_abs_self _) hexp)

theorem highWeight_irrational_of_relative_cost
    (s : ℕ) (hs : 7 ≤ s) (α : ℝ) (A B : ℕ → ℤ)
    (index : ℕ → ℕ) (hindex : Tendsto index atTop atTop)
    (D W S : ℕ → ℝ)
    (hD : ∀ n, 0 ≤ D n) (hW : ∀ n, 0 ≤ W n)
    (hbound : ∀ᶠ n in atTop,
      |(A n : ℝ) * α - (B n : ℝ)| ≤ D n * W n * S n)
    (hden : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      D n ≤ Real.exp (((s : ℝ) + ε) * (index n : ℝ)))
    (hcost : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      W n ≤ Real.exp (ε * (index n : ℝ)))
    (hraw : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      S n ≤ Real.exp ((-highWeightDecay s + ε) * (index n : ℝ)))
    (hnonzero : ∀ N, ∃ n ≥ N, (A n : ℝ) * α - (B n : ℝ) ≠ 0) :
    Irrational α := by
  have hsmall := smallness_of_eventual_relative_cost s hs index hindex D W S
    (fun n => (A n : ℝ) * α - (B n : ℝ)) hD hW hbound hden hcost hraw
  have hirr := no_rational_representation_of_small_linear_forms α A B
    (fun _ => 1) (by simp) (by simpa using hsmall) hnonzero
  rw [irrational_iff_ne_rational]
  intro p d hd heq
  exact hirr ⟨p, d, hd, heq⟩

theorem oddZeta_irrational_of_relative_cost
    (k : ℕ) (hk : 3 ≤ k) (A B : ℕ → ℤ)
    (index : ℕ → ℕ) (hindex : Tendsto index atTop atTop)
    (d M Γ : ℕ → ℕ) (S : ℕ → ℝ)
    (hbound : ∀ᶠ n in atTop,
      |(A n : ℝ) * oddZetaValue k - (B n : ℝ)| ≤
        (d n : ℝ) ^ (2 * k + 1) * ((M n : ℝ) / (Γ n : ℝ)) * S n)
    (hden : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (d n : ℝ) ^ (2 * k + 1) ≤
        Real.exp ((((2 * k + 1 : ℕ) : ℝ) + ε) * (index n : ℝ)))
    (hcost : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (M n : ℝ) / (Γ n : ℝ) ≤ Real.exp (ε * (index n : ℝ)))
    (hraw : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      S n ≤ Real.exp ((-highWeightDecay (2 * k + 1) + ε) * (index n : ℝ)))
    (hnonzero : ∀ N, ∃ n ≥ N,
      (A n : ℝ) * oddZetaValue k - (B n : ℝ) ≠ 0) :
    Irrational (oddZetaValue k) := by
  exact highWeight_irrational_of_relative_cost (2 * k + 1) (by omega)
    (oddZetaValue k) A B index hindex
    (fun n => (d n : ℝ) ^ (2 * k + 1))
    (fun n => (M n : ℝ) / (Γ n : ℝ)) S
    (fun _ => by positivity) (fun _ => by positivity)
    hbound hden hcost hraw hnonzero

end OddZeta
