import OddZeta.IntegralFramedComparison

namespace OddZeta

theorem harmonicLcm_dvd_of_le {m M : ℕ} (h : m ≤ M) :
    harmonicLcm m ∣ harmonicLcm M := by
  apply Finset.lcm_dvd
  intro j hj
  exact successor_dvd_harmonicLcm (lt_of_lt_of_le (Finset.mem_range.mp hj) h)

theorem scaledHarmonicPower_change_scale (s m M k : ℕ)
    (hk : k ≤ m) (hm : m ≤ M) :
    scaledHarmonicPower s M k =
      (((harmonicLcm M / harmonicLcm m) ^ s : ℕ) : ℤ) *
        scaledHarmonicPower s m k := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_pow]
  rw [scaledHarmonicPower_cast s M k (hk.trans hm),
    scaledHarmonicPower_cast s m k hk]
  have hq : ((harmonicLcm M / harmonicLcm m : ℕ) : ℚ) *
      (harmonicLcm m : ℚ) = (harmonicLcm M : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel (harmonicLcm_dvd_of_le hm)
  rw [← mul_assoc, ← mul_pow, hq]

def rowHankelScale (s n a : ℕ) (i : Fin (n + 1)) : ℕ :=
  harmonicLcm (a + i.val + n) ^ s

def rowHankelFactor (s n a : ℕ) (i : Fin (n + 1)) : ℕ :=
  (harmonicLcm (a + 2 * n) / harmonicLcm (a + i.val + n)) ^ s

def rowHankelSaving (s n a : ℕ) : ℕ :=
  ∏ i : Fin (n + 1), rowHankelFactor s n a i

def rowHankelCost (s n a : ℕ) : ℕ :=
  ∏ i : Fin (n + 1), rowHankelScale s n a i

def rowHankelMatrix (s n a : ℕ) (y : ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := fun i j =>
  (rowHankelScale s n a i : ℤ) * y -
    scaledHarmonicPower s (a + i.val + n) (a + i.val + j.val)

noncomputable def rowHankelIntegerA (s n a : ℕ) : ℤ :=
  (rowHankelMatrix s n a 1).det - (rowHankelMatrix s n a 0).det

noncomputable def rowHankelIntegerB (s n a : ℕ) : ℤ :=
  (rowHankelMatrix s n a 0).det

theorem rowHankelFactor_mul_scale (s n a : ℕ) (i : Fin (n + 1)) :
    rowHankelFactor s n a i * rowHankelScale s n a i =
      oddHankelEntryScale s n a := by
  have hi : a + i.val + n ≤ a + 2 * n := by have h := i.isLt; omega
  unfold rowHankelFactor rowHankelScale oddHankelEntryScale
  rw [← mul_pow, Nat.div_mul_cancel (harmonicLcm_dvd_of_le hi)]

theorem rowHankelSaving_mul_cost (s n a : ℕ) :
    rowHankelSaving s n a * rowHankelCost s n a =
      oddHankelEntryScale s n a ^ (n + 1) := by
  unfold rowHankelSaving rowHankelCost
  rw [← Finset.prod_mul_distrib]
  simp only [rowHankelFactor_mul_scale, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem rowHankelSaving_ne_zero (s n a : ℕ) : rowHankelSaving s n a ≠ 0 := by
  intro h
  have hc := rowHankelSaving_mul_cost s n a
  rw [h, zero_mul] at hc
  exact pow_ne_zero _ (oddHankelEntryScale_ne_zero s n a) hc.symm

theorem rowHankel_determinant_factorization (s n a : ℕ) (y : ℤ) :
    (arithmeticMatrixShift (oddHankelIntegerBase s n a)
      ((oddHankelEntryScale s n a : ℤ) * y)).det =
      (rowHankelSaving s n a : ℤ) * (rowHankelMatrix s n a y).det := by
  have hm : arithmeticMatrixShift (oddHankelIntegerBase s n a)
      ((oddHankelEntryScale s n a : ℤ) * y) =
      fun i j => (rowHankelFactor s n a i : ℤ) * rowHankelMatrix s n a y i j := by
    ext i j
    have hi : a + i.val + n ≤ a + 2 * n := by have h := i.isLt; omega
    have hj : a + i.val + j.val ≤ a + i.val + n := by have h := j.isLt; omega
    have hh := scaledHarmonicPower_change_scale s (a + i.val + n)
      (a + 2 * n) (a + i.val + j.val) hj hi
    have hs : (oddHankelEntryScale s n a : ℤ) =
        (rowHankelFactor s n a i : ℤ) * (rowHankelScale s n a i : ℤ) := by
      exact_mod_cast (rowHankelFactor_mul_scale s n a i).symm
    change (oddHankelEntryScale s n a : ℤ) * y -
      scaledHarmonicPower s (a + 2 * n) (a + i.val + j.val) = _
    rw [hs, hh]
    change (rowHankelFactor s n a i : ℤ) * (rowHankelScale s n a i : ℤ) * y -
      (rowHankelFactor s n a i : ℤ) *
        scaledHarmonicPower s (a + i.val + n) (a + i.val + j.val) = _
    unfold rowHankelMatrix
    ring
  rw [hm]
  convert! Matrix.det_mul_column (fun i => (rowHankelFactor s n a i : ℤ))
    (rowHankelMatrix s n a y) using 1
  simp [rowHankelSaving]

theorem rowHankel_coefficient_factorization (s n a : ℕ) :
    oddHankelIntegerA s n a =
      (rowHankelSaving s n a : ℤ) * rowHankelIntegerA s n a ∧
    oddHankelIntegerB s n a =
      (rowHankelSaving s n a : ℤ) * rowHankelIntegerB s n a := by
  have h1 := rowHankel_determinant_factorization s n a 1
  have h0 := rowHankel_determinant_factorization s n a 0
  simp only [mul_one, mul_zero] at h1 h0
  constructor
  · unfold oddHankelIntegerA rowHankelIntegerA
    rw [h1, h0]
    ring
  · exact h0

theorem rowHankelSaving_dvd_content (s n a : ℕ) :
    (rowHankelSaving s n a : ℤ) ∣
      (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ) := by
  apply (divides_coefficient_content_iff _ _ _).mpr
  have h := rowHankel_coefficient_factorization s n a
  exact ⟨⟨rowHankelIntegerA s n a, h.1⟩, ⟨rowHankelIntegerB s n a, h.2⟩⟩

theorem rowHankel_content_factorization (s n a : ℕ) :
    Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) =
      rowHankelSaving s n a * Int.gcd (rowHankelIntegerA s n a) (rowHankelIntegerB s n a) := by
  have hf := rowHankel_coefficient_factorization s n a
  have h := framed_comparison_content
    (oddHankelIntegerA s n a) (oddHankelIntegerB s n a)
    (rowHankelIntegerA s n a) (rowHankelIntegerB s n a)
    (rowHankelSaving s n a : ℤ) (LinearEquiv.refl ℤ (ℤ × ℤ)) (by
      intro z
      change oddHankelIntegerA s n a * z.1 + oddHankelIntegerB s n a * z.2 =
        (rowHankelSaving s n a : ℤ) *
          (rowHankelIntegerA s n a * z.1 + rowHankelIntegerB s n a * z.2)
      rw [hf.1, hf.2]
      ring)
  simpa only [Int.natAbs_natCast] using h

theorem rowHankel_prime_cost (s n a p : ℕ) (hp : p.Prime) :
    (rowHankelCost s n a).factorization p =
      ∑ i : Fin (n + 1), s * Nat.log p (a + i.val + n) := by
  unfold rowHankelCost rowHankelScale
  rw [Nat.factorization_prod_apply (fun i _ =>
    pow_ne_zero s (harmonicLcm_ne_zero (a + i.val + n)))]
  simp [harmonicLcm_eq_lcmUpto,
    Nat.factorization_pow, Nat.factorization_lcmUpto _ hp]

theorem rowHankel_log_cost_lower (s n a : ℕ) :
    (∑ i : Fin (n + 1), (s : ℝ) *
      ((a + i.val + n : ℕ) * Real.log 2 - Real.log (a + i.val + n + 1 : ℕ))) ≤
      Real.log (rowHankelCost s n a : ℝ) := by
  unfold rowHankelCost
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_le_sum
    intro i _
    simp only [rowHankelScale, Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left (harmonicLcm_log_lower (a + i.val + n))
      (by positivity)
  · intro i _
    exact_mod_cast pow_ne_zero s (harmonicLcm_ne_zero (a + i.val + n))

end OddZeta
