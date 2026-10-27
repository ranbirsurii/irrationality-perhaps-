import OddZeta.AperyFive

namespace OddZeta

theorem aperySummand_nonneg (n k : ℕ) : 0 ≤ aperySummand n k := by
  unfold aperySummand
  positivity

theorem aperyA_ge_one (n : ℕ) : (1 : ℚ) ≤ aperyA n := by
  have h := Finset.single_le_sum (f := aperySummand n)
    (fun k _ => aperySummand_nonneg n k)
    (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  simpa [aperyA, aperySummand] using h

theorem aperySummand_successive_ratio_cleared (n k : ℕ) (hk : k ≤ n) :
    aperySummand n (k + 1) * ((k : ℚ) + 1) ^ 4 =
      aperySummand n k * ((n : ℚ) - k) ^ 2 * ((n : ℚ) + k + 1) ^ 2 := by
  have h1 : (Nat.choose n (k + 1) : ℚ) * ((k : ℚ) + 1) =
      (Nat.choose n k : ℚ) * ((n : ℚ) - k) := by
    have h := Nat.choose_succ_right_eq n k
    have hc := congrArg (fun x : ℕ => (x : ℚ)) h
    simpa [Nat.cast_sub hk] using hc
  have h2 : (Nat.choose (n + k + 1) (k + 1) : ℚ) * ((k : ℚ) + 1) =
      (Nat.choose (n + k) k : ℚ) * ((n : ℚ) + k + 1) := by
    have h := Nat.add_one_mul_choose_eq (n + k) k
    have hc := congrArg (fun x : ℕ => (x : ℚ)) h.symm
    simpa [mul_comm] using hc
  have he : n + (k + 1) = n + k + 1 := by omega
  unfold aperySummand
  rw [he]
  calc
    _ = ((Nat.choose n (k + 1) : ℚ) * ((k : ℚ) + 1)) ^ 2 *
        ((Nat.choose (n + k + 1) (k + 1) : ℚ) * ((k : ℚ) + 1)) ^ 2 := by ring
    _ = _ := by rw [h1, h2]; ring

def aperyELocalPolynomial (eta h2p h2 h2m h3p h3 h3m h4 h5 : ℚ) : ℚ :=
  let second := h2p - 2 * h2 - h2m
  let third := -h3p + 2 * h3 - h3m
  let regular0 := 2 * eta ^ 2 - second
  let regular1 := -(4 : ℚ) / 3 * eta ^ 3 + 2 * eta * second + (2 : ℚ) / 3 * third
  let pole0 := h2 + h2m
  let pole1 := 2 * h3 - 2 * h3m
  4 * h5 - 6 * eta * h4 + 2 * (regular0 + pole0) * h3 +
    (regular1 - 2 * eta * pole0 + pole1) * h2

def aperyELocal (n k : ℕ) : ℚ :=
  aperyELocalPolynomial (aperyEta n k)
    (harmonicTwo (n + k)) (harmonicTwo k) (harmonicTwo (n - k))
    (harmonicThree (n + k)) (harmonicThree k) (harmonicThree (n - k))
    (harmonicFour k) (harmonicFive k)

theorem aperyE_eq_weighted_local (n : ℕ) :
    aperyE n = ∑ k ∈ Finset.range (n + 1), aperySummand n k * aperyELocal n k := by
  unfold aperyE
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold aperyELocal aperyELocalPolynomial aperyR1Pole4 aperyR1Pole3
    aperyR1Pole2 aperyR1Pole1 aperyLocalRegular0 aperyLocalRegular1
    aperyLocalSecond aperyLocalThird aperyPoleRegular0 aperyPoleRegular1
  dsimp
  ring

theorem aperyELocalPolynomial_at_saddle (z2 z3 z4 z5 : ℚ) :
    aperyELocalPolynomial 0 z2 z2 z2 z3 z3 z3 z4 z5 = 4 * z5 + 8 * z2 * z3 := by
  unfold aperyELocalPolynomial
  dsimp
  ring

theorem aperyProjected_saddle_constant (z2 z3 z5 : ℚ) :
    -4 * z5 - (7 : ℚ) / 24 * (4 * z5 + 8 * z2 * z3) =
      -((31 : ℚ) / 6 * z5 + (7 : ℚ) / 3 * z2 * z3) := by
  ring

theorem aperyProjectedForm_le_neg_four (n : ℕ) (alpha : ℝ)
    (halpha : 0 ≤ alpha) (hE : 0 ≤ aperyE n) :
    aperyProjectedForm n alpha ≤ -4 * alpha := by
  have hA : (1 : ℝ) ≤ (aperyA n : ℝ) := by exact_mod_cast aperyA_ge_one n
  have hER : (0 : ℝ) ≤ (aperyE n : ℝ) := by exact_mod_cast hE
  have hcoef : (aperyProjectedA n : ℝ) = -4 * (aperyA n : ℝ) := by
    exact_mod_cast aperyProjectedA_eq_rationalCoefficient n
  unfold aperyProjectedForm aperyProjectedB
  rw [hcoef]
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) halpha]

theorem aperyProjectedForm_abs_lower (n : ℕ) (alpha : ℝ)
    (halpha : 0 ≤ alpha) (hE : 0 ≤ aperyE n) :
    4 * alpha ≤ |aperyProjectedForm n alpha| := by
  have h := aperyProjectedForm_le_neg_four n alpha halpha hE
  rw [abs_of_nonpos (by linarith : aperyProjectedForm n alpha ≤ 0)]
  linarith

theorem positive_integer_form_abs_lower (a b : ℤ) (alpha : ℝ)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (halpha : 0 ≤ alpha) :
    alpha ≤ |(a : ℝ) * alpha + (b : ℝ)| := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  rw [abs_of_nonneg (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr haR) halpha]

def twoGridNumerator (n : ℕ) (t : ℚ) : ℚ :=
  ∏ j ∈ Finset.range (2 * n),
    (t - ((j : ℚ) + 1) / 2) * (t + (n : ℚ) + ((j : ℚ) + 1) / 2)

def twoGridKernel (n : ℕ) (t : ℚ) : ℚ :=
  (Nat.factorial n : ℚ) * (2 * t + (n : ℚ)) * twoGridNumerator n t /
    (∏ j ∈ Finset.range (n + 1), (t + (j : ℚ)) ^ 5)

theorem twoGridNumerator_zero (n i : ℕ) (hi : i < 2 * n) :
    twoGridNumerator n (((i : ℚ) + 1) / 2) = 0 := by
  unfold twoGridNumerator
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
  simp

theorem twoGridKernel_zero (n i : ℕ) (hi : i < 2 * n) :
    twoGridKernel n (((i : ℚ) + 1) / 2) = 0 := by
  simp [twoGridKernel, twoGridNumerator_zero n i hi]

theorem twoGridNumerator_reflection (n : ℕ) (t : ℚ) :
    twoGridNumerator n (-t - (n : ℚ)) = twoGridNumerator n t := by
  unfold twoGridNumerator
  apply Finset.prod_congr rfl
  intro j _
  ring

noncomputable def twoGridSaddlePolynomial (x : ℝ) : ℝ :=
  x ^ 8 + 4 * x ^ 7 - 14 * x ^ 5 - 14 * x ^ 4 + 8 * x ^ 2 + 5 * x + 1

theorem twoGrid_saddle_polynomial_identity (x : ℝ) :
    x ^ 7 * (x + 2) ^ 2 - (x - 1) ^ 2 * (x + 1) ^ 7 =
      -twoGridSaddlePolynomial x := by
  unfold twoGridSaddlePolynomial
  ring

theorem twoGrid_naive_normalization_growth_constant :
    0 < 34 * Real.log 2 - 21 * Real.log 3 := by
  have h : (3 : ℝ) ^ 21 < 2 ^ 34 := by norm_num
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 3 ^ 21) h
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

end OddZeta
