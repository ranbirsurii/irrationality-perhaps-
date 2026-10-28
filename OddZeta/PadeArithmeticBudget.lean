import OddZeta.PoisedKernelPositivity
import Mathlib.Data.Nat.Choose.Cast

namespace OddZeta

def normalizedPoisedTopMagnitude (s n m j : ℕ) : ℚ :=
  (n.factorial : ℚ) ^ s * ((j + m).factorial : ℚ) * ((n - j + m).factorial : ℚ) /
    ((m.factorial : ℚ) ^ 2 * (j.factorial : ℚ) ^ (s + 1) *
      ((n - j).factorial : ℚ) ^ (s + 1))

theorem normalizedPoisedTopMagnitude_eq_choose (s n m j : ℕ) (hj : j ≤ n) :
    normalizedPoisedTopMagnitude s n m j =
      (n.choose j : ℚ) ^ s * ((j + m).choose m : ℚ) *
        ((n - j + m).choose m : ℚ) := by
  rw [Nat.cast_choose ℚ hj, Nat.cast_choose ℚ (Nat.le_add_left m j),
    Nat.cast_choose ℚ (Nat.le_add_left m (n - j))]
  simp only [Nat.add_sub_cancel_right]
  unfold normalizedPoisedTopMagnitude
  simp only [pow_succ, div_pow, mul_pow, div_mul_eq_mul_div,
    mul_div_assoc, div_div]
  field_simp

theorem normalizedPoisedTopMagnitude_integral (s n m j : ℕ) (hj : j ≤ n) :
    ∃ z : ℤ, normalizedPoisedTopMagnitude s n m j = (z : ℚ) := by
  rw [normalizedPoisedTopMagnitude_eq_choose s n m j hj]
  refine ⟨((n.choose j) ^ s * (j + m).choose m * (n - j + m).choose m : ℕ), ?_⟩
  norm_cast

theorem poisedRationalKernel_block_succ (r n m : ℕ) (t : ℚ) :
    poisedRationalKernel r n (m + 1) t =
      poisedRationalKernel r n m t * (t - (m + 1 : ℕ)) *
        (t + n + (m + 1 : ℕ)) := by
  simp only [poisedRationalKernel, Finset.prod_range_succ]
  ring

theorem poised_nonnegative_combination {ι : Type*} [Fintype ι]
    (r n : ℕ) (m : ι → ℕ) (w : ι → ℚ) (a : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hne : ∃ i, 0 < w i)
    (hs : ∀ i, HasSum (fun k : ℕ =>
      (poisedRationalKernel r n (m i) ((k + 1 : ℕ) : ℚ) : ℝ)) (a i)) :
    HasSum (fun k : ℕ => ∑ i, (w i : ℝ) *
      (poisedRationalKernel r n (m i) ((k + 1 : ℕ) : ℚ) : ℝ))
      (∑ i, (w i : ℝ) * a i) ∧ 0 < ∑ i, (w i : ℝ) * a i := by
  constructor
  · exact hasSum_sum (fun i _ => (hs i).mul_left (w i : ℝ))
  · have ha (i : ι) : 0 < a i := poisedRationalKernel_hasSum_pos r n (m i) (a i) (hs i)
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (by exact_mod_cast hw i) (ha i).le
    · obtain ⟨i, hi⟩ := hne
      exact ⟨i, Finset.mem_univ i, mul_pos (by exact_mod_cast hi) (ha i)⟩

theorem primitive_clearing_cost_invariant (D c : ℕ) (hc : c ≠ 0) (a b : ℤ)
    (hg : Int.gcd a b ≠ 0) :
    ((c * D : ℕ) : ℚ) / (Int.gcd ((c : ℤ) * a) ((c : ℤ) * b) : ℚ) =
      (D : ℚ) / (Int.gcd a b : ℚ) := by
  rw [Int.gcd_mul_left]
  simp only [Int.natAbs_natCast, Nat.cast_mul]
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hgQ : (Int.gcd a b : ℚ) ≠ 0 := by exact_mod_cast hg
  field_simp

end OddZeta
