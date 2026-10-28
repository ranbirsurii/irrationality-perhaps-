import OddZeta.PadeArithmeticBudget

namespace OddZeta

theorem harmonicPower_mono_index (s : ℕ) {a b : ℕ} (h : a ≤ b) :
    harmonicPower s a ≤ harmonicPower s b := by
  unfold harmonicPower
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun _ _ _ => by positivity)

theorem harmonicPower_subadditive (s a b : ℕ) :
    harmonicPower s (a + b) ≤ harmonicPower s a + harmonicPower s b := by
  unfold harmonicPower
  rw [Finset.sum_range_add]
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro k _
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast (show k + 1 ≤ a + k + 1 by omega)

theorem harmonicPower_positive (s n : ℕ) (hn : 0 < n) : 0 < harmonicPower s n := by
  have h := harmonicPower_mono_index s (show 1 ≤ n by omega)
  have h1 : harmonicPower s 1 = 1 := by simp [harmonicPower]
  rw [h1] at h
  linarith

def padeFiveLogSlope (n m j : ℕ) : ℚ :=
  harmonicPower 1 (n - j + m) - harmonicPower 1 (j + m) +
    6 * (harmonicPower 1 j - harmonicPower 1 (n - j))

def padeFiveLogCurvature (n m j : ℕ) : ℚ :=
  6 * (harmonicPower 2 j + harmonicPower 2 (n - j)) -
    harmonicPower 2 (j + m) - harmonicPower 2 (n - j + m)

theorem padeFiveLogCurvature_lower (n m j : ℕ) (hm : m ≤ n) (hj : j ≤ n) :
    3 * (harmonicPower 2 j + harmonicPower 2 (n - j)) ≤
      padeFiveLogCurvature n m j := by
  have h1 := harmonicPower_subadditive 2 j m
  have h2 := harmonicPower_subadditive 2 (n - j) m
  have h3 := harmonicPower_subadditive 2 j (n - j)
  rw [Nat.add_sub_of_le hj] at h3
  have h4 := harmonicPower_mono_index 2 hm
  unfold padeFiveLogCurvature
  linarith

def padeFiveLocalAmplitude (n m j : ℕ) : ℚ :=
  (padeFiveLogSlope n m j ^ 2 + padeFiveLogCurvature n m j) / 2

theorem padeFiveLocalAmplitude_positive (n m j : ℕ) (hn : 0 < n)
    (hm : m ≤ n) (hj : j ≤ n) : 0 < padeFiveLocalAmplitude n m j := by
  have hp := harmonicPower_positive 2 n hn
  have hs := harmonicPower_subadditive 2 j (n - j)
  rw [Nat.add_sub_of_le hj] at hs
  have hc := padeFiveLogCurvature_lower n m j hm hj
  have hsq := sq_nonneg (padeFiveLogSlope n m j)
  unfold padeFiveLocalAmplitude
  linarith

theorem padeFiveLocalAmplitude_lower (n m j : ℕ) (hm : m ≤ n) (hj : j ≤ n) :
    3 * harmonicPower 2 n / 2 ≤ padeFiveLocalAmplitude n m j := by
  have hs := harmonicPower_subadditive 2 j (n - j)
  rw [Nat.add_sub_of_le hj] at hs
  have hc := padeFiveLogCurvature_lower n m j hm hj
  have hsq := sq_nonneg (padeFiveLogSlope n m j)
  unfold padeFiveLocalAmplitude
  linarith

def padeFiveLocalCoefficient (n m j : ℕ) : ℚ :=
  (-1 : ℚ) ^ (m + j) * (n.choose j : ℚ) ^ 5 *
    ((j + m).choose m : ℚ) * ((n - j + m).choose m : ℚ) *
      padeFiveLocalAmplitude n m j

theorem padeFiveLocalCoefficient_signed_positive (n m j : ℕ) (hn : 0 < n)
    (hm : m ≤ n) (hj : j ≤ n) :
    0 < (-1 : ℚ) ^ (m + j) * padeFiveLocalCoefficient n m j := by
  have hsign : (-1 : ℚ) ^ (m + j) * (-1 : ℚ) ^ (m + j) = 1 := by
    rw [← mul_pow]
    norm_num
  have h1 : 0 < (n.choose j : ℚ) := by exact_mod_cast Nat.choose_pos hj
  have h2 : 0 < ((j + m).choose m : ℚ) := by
    exact_mod_cast Nat.choose_pos (show m ≤ j + m by omega)
  have h3 : 0 < ((n - j + m).choose m : ℚ) := by
    exact_mod_cast Nat.choose_pos (show m ≤ n - j + m by omega)
  have h4 := padeFiveLocalAmplitude_positive n m j hn hm hj
  have heq : (-1 : ℚ) ^ (m + j) * padeFiveLocalCoefficient n m j =
      (n.choose j : ℚ) ^ 5 * ((j + m).choose m : ℚ) *
        ((n - j + m).choose m : ℚ) * padeFiveLocalAmplitude n m j := by
    unfold padeFiveLocalCoefficient
    calc
      _ = ((-1 : ℚ) ^ (m + j) * (-1 : ℚ) ^ (m + j)) *
          ((n.choose j : ℚ) ^ 5 * ((j + m).choose m : ℚ) *
          ((n - j + m).choose m : ℚ) * padeFiveLocalAmplitude n m j) := by ring
      _ = _ := by rw [hsign, one_mul]
  rw [heq]
  positivity

end OddZeta
