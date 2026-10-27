import Mathlib

open Filter

def IsIrrationalReal (x : ℝ) : Prop :=
  ¬ ∃ p d : ℤ, d ≠ 0 ∧ x = (p : ℝ) / (d : ℝ)

/-- The real part of the Riemann zeta value at the positive odd integer `2k+1`. -/
noncomputable def oddZetaValue (k : ℕ) : ℝ :=
  (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re

theorem int_eq_zero_of_abs_cast_lt_one {z : ℤ}
    (h : |(z : ℝ)| < 1) : z = 0 := by
  have hbounds := abs_lt.mp h
  have hlow : (-1 : ℤ) < z := by exact_mod_cast hbounds.1
  have hhigh : z < 1 := by exact_mod_cast hbounds.2
  omega

theorem integer_sequence_eventually_zero
    (u : ℕ → ℤ)
    (hlim : Tendsto (fun n => (u n : ℝ)) atTop (nhds 0)) :
    ∃ N, ∀ n ≥ N, u n = 0 := by
  have hBound := (Metric.tendsto_atTop.1 hlim) 1 (by norm_num)
  rcases hBound with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  apply int_eq_zero_of_abs_cast_lt_one
  have hdist : dist (u n : ℝ) 0 < (1 : ℝ) := hN n hn
  simpa [Real.dist_eq] using hdist

theorem no_rational_representation_of_small_linear_forms
    (α : ℝ)
    (A B q : ℕ → ℤ)
    (hq : ∀ n, q n ≠ 0)
    (hsmall :
      Tendsto
        (fun n => (q n : ℝ) * ((A n : ℝ) * α - (B n : ℝ)))
        atTop (nhds 0))
    (hnonzero :
      ∀ N, ∃ n ≥ N, (A n : ℝ) * α - (B n : ℝ) ≠ 0) :
    IsIrrationalReal α := by
  intro hr
  rcases hr with ⟨p, d, hd, hα⟩
  let m : ℕ → ℤ := fun n => q n * (p * A n - d * B n)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hEq (n : ℕ) :
      (m n : ℝ) = ((d : ℝ) * (q n : ℝ)) *
        ((A n : ℝ) * α - (B n : ℝ)) := by
    dsimp [m]
    rw [hα]
    push_cast
    field_simp [hdR]
  have hscaled :
      Tendsto
        (fun n => ((d : ℝ) * (q n : ℝ)) *
          ((A n : ℝ) * α - (B n : ℝ)))
        atTop (nhds 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => (d : ℝ)) atTop (nhds (d : ℝ)) :=
      tendsto_const_nhds
    have h := hconst.mul hsmall
    simpa [mul_assoc] using h
  have hmlim : Tendsto (fun n => (m n : ℝ)) atTop (nhds 0) := by
    convert hscaled using 1
    ext n
    exact hEq n
  obtain ⟨N, hzero⟩ := integer_sequence_eventually_zero m hmlim
  obtain ⟨n, hnN, hform⟩ := hnonzero N
  have hm : m n ≠ 0 := by
    intro hm
    have hcast : (m n : ℝ) = 0 := by exact_mod_cast hm
    rw [hEq n] at hcast
    have hqR : (q n : ℝ) ≠ 0 := by exact_mod_cast hq n
    have hproduct :
        ((d : ℝ) * (q n : ℝ)) *
          ((A n : ℝ) * α - (B n : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hdR hqR) hform
    exact hproduct hcast
  exact hm (hzero n hnN)

/-- Conditional odd-zeta application. Its assumptions are arbitrarily-late
nonvanishing and decay of the denominator-scaled forms. -/
theorem oddZetaValue_irrational_of_small_linear_forms
    (k : ℕ)
    (A B q : ℕ → ℤ)
    (hq : ∀ n, q n ≠ 0)
    (hsmall :
      Tendsto
        (fun n => (q n : ℝ) *
          ((A n : ℝ) * oddZetaValue k - (B n : ℝ)))
        atTop (nhds 0))
    (hnonzero :
      ∀ N, ∃ n ≥ N,
        (A n : ℝ) * oddZetaValue k - (B n : ℝ) ≠ 0) :
    IsIrrationalReal (oddZetaValue k) :=
  no_rational_representation_of_small_linear_forms
    (oddZetaValue k) A B q hq hsmall hnonzero

/-- Exponential denominator growth and linear-form decay imply the
denominator-scaled forms tend to zero whenever the decay exponent is larger.
The constants may absorb any finite initial segment. -/
theorem tendsto_scaled_of_exponential_bounds
    (q : ℕ → ℕ) (L : ℕ → ℝ) (alpha beta Cq CL : ℝ)
    (hgap : beta < alpha) (hCq : 0 ≤ Cq) (hCL : 0 ≤ CL)
    (hq : ∀ n, (q n : ℝ) ≤ Cq * Real.exp (beta * (n : ℝ)))
    (hL : ∀ n, |L n| ≤ CL * Real.exp (-alpha * (n : ℝ))) :
    Tendsto (fun n => (q n : ℝ) * L n) atTop (nhds 0) := by
  let delta := alpha - beta
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hexp :
      Tendsto (fun n : ℕ => Real.exp (-delta * (n : ℝ))) atTop (nhds 0) := by
    have harg :
        Tendsto (fun n : ℕ => delta * (n : ℝ)) atTop atTop := by
      exact Tendsto.const_mul_atTop hdelta tendsto_natCast_atTop_atTop
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg).congr fun n => by
      simp [neg_mul]
  have hbound :
      Tendsto (fun n : ℕ => Cq * CL * Real.exp (-delta * (n : ℝ)))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  have hprod (n : ℕ) :
      |(q n : ℝ) * L n| ≤ Cq * CL * Real.exp (-delta * (n : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      (q n : ℝ) * |L n| ≤
          (Cq * Real.exp (beta * (n : ℝ))) *
            (CL * Real.exp (-alpha * (n : ℝ))) :=
        mul_le_mul (hq n) (hL n) (abs_nonneg _)
          (mul_nonneg hCq (le_of_lt (Real.exp_pos _)))
      _ = Cq * CL *
          (Real.exp (beta * (n : ℝ)) * Real.exp (-alpha * (n : ℝ))) := by ring
      _ = Cq * CL * Real.exp (beta * (n : ℝ) + -alpha * (n : ℝ)) := by
        rw [← Real.exp_add]
      _ = Cq * CL * Real.exp (-delta * (n : ℝ)) := by
        congr 2
        dsimp [delta]
        ring
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hbound) ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hdist : dist ((q n : ℝ) * L n) 0 ≤
      Cq * CL * Real.exp (-delta * (n : ℝ)) := by
    simpa [Real.dist_eq] using hprod n
  have hboundN : Cq * CL * Real.exp (-delta * (n : ℝ)) < ε := by
    have h := hN n hn
    have h' : |Cq * CL * Real.exp (-delta * (n : ℝ))| < ε := by
      simpa using h
    simpa [abs_of_nonneg hCq, abs_of_nonneg hCL] using h'
  exact lt_of_le_of_lt hdist hboundN

/-- The integer-smallness irrationality criterion with explicit exponential
rate hypotheses in place of a black-box convergence assumption. -/
theorem irrational_of_exponential_linear_forms
    (alphaValue : ℝ) (A B : ℕ → ℤ) (q : ℕ → ℕ)
    (alpha beta Cq CL : ℝ)
    (hqne : ∀ n, q n ≠ 0)
    (hgap : beta < alpha) (hCq : 0 ≤ Cq) (hCL : 0 ≤ CL)
    (hq : ∀ n, (q n : ℝ) ≤ Cq * Real.exp (beta * (n : ℝ)))
    (hdecay : ∀ n,
      |(A n : ℝ) * alphaValue - (B n : ℝ)| ≤
        CL * Real.exp (-alpha * (n : ℝ)))
    (hnonzero : ∀ N, ∃ n ≥ N,
      (A n : ℝ) * alphaValue - (B n : ℝ) ≠ 0) :
    IsIrrationalReal alphaValue := by
  apply no_rational_representation_of_small_linear_forms
    alphaValue A B (fun n => (q n : ℤ)) ?_ ?_ hnonzero
  · intro n
    exact_mod_cast hqne n
  · apply tendsto_scaled_of_exponential_bounds
      (fun n => q n) (fun n => (A n : ℝ) * alphaValue - (B n : ℝ))
      alpha beta Cq CL hgap hCq hCL hq hdecay

/-- The decay and denominator slopes stated in the manuscript. -/
noncomputable def manuscriptDecaySlope (n : ℕ) : ℝ :=
  4 * (n : ℝ) * Real.log (1 + Real.sqrt 2)

noncomputable def manuscriptDenominatorSlope (n : ℕ) : ℝ :=
  2 * (n : ℝ) + 1

theorem manuscript_log_bound :
    (3 : ℝ) / 4 < Real.log (1 + Real.sqrt 2) := by
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num [Real.sq_sqrt]
  have hlog := Real.lt_log_one_add_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2)
  have hr : (3 : ℝ) / 4 < 2 * Real.sqrt 2 / (Real.sqrt 2 + 2) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2 + 2)]
    nlinarith [hs, Real.sqrt_nonneg (2 : ℝ)]
  linarith

theorem manuscript_rate_gap (n : ℕ) (hn : 1 ≤ n) :
    manuscriptDenominatorSlope n < manuscriptDecaySlope n := by
  have hlog := manuscript_log_bound
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul : 3 * (n : ℝ) < 4 * (n : ℝ) * Real.log (1 + Real.sqrt 2) := by
    have := mul_lt_mul_of_pos_left hlog (show 0 < 4 * (n : ℝ) by positivity)
    nlinarith
  have hsmall : 2 * (n : ℝ) + 1 ≤ 3 * (n : ℝ) := by nlinarith
  unfold manuscriptDenominatorSlope manuscriptDecaySlope
  linarith
