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
