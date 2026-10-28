import OddZeta.MellinRationalMoments

namespace OddZeta

def poisedRationalKernel (r n m : ℕ) (t : ℚ) : ℚ :=
  (2 * t + n) ^ (Nat.mod n 2) *
    (∏ v ∈ Finset.range m, (t - (v + 1 : ℕ)) * (t + n + (v + 1 : ℕ))) /
      ∏ j ∈ Finset.range (n + 1), (t + (j : ℚ)) ^ (2 * r + 1)

theorem poisedRationalKernel_zero_integer (r n m k : ℕ) (hk : k + 1 ≤ m) :
    poisedRationalKernel r n m ((k + 1 : ℕ) : ℚ) = 0 := by
  have hz : (∏ v ∈ Finset.range m,
      (((k + 1 : ℕ) : ℚ) - (v + 1 : ℕ)) *
        (((k + 1 : ℕ) : ℚ) + n + (v + 1 : ℕ))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : k < m))
    simp
  unfold poisedRationalKernel
  rw [hz]
  simp

theorem poisedRationalKernel_pos_integer (r n m k : ℕ) (hk : m < k + 1) :
    0 < poisedRationalKernel r n m ((k + 1 : ℕ) : ℚ) := by
  unfold poisedRationalKernel
  apply div_pos
  · apply mul_pos
    · apply pow_pos
      positivity
    · apply Finset.prod_pos
      intro v hv
      have hv' := Finset.mem_range.mp hv
      apply mul_pos
      · have h : (v + 1 : ℕ) < k + 1 := by omega
        exact sub_pos.mpr (by exact_mod_cast h)
      · positivity
  · apply Finset.prod_pos
    intro j _
    apply pow_pos
    positivity

theorem poisedRationalKernel_nonneg_integer (r n m k : ℕ) :
    0 ≤ poisedRationalKernel r n m ((k + 1 : ℕ) : ℚ) := by
  by_cases hk : m < k + 1
  · exact (poisedRationalKernel_pos_integer r n m k hk).le
  · rw [poisedRationalKernel_zero_integer r n m k (by omega)]

theorem hasSum_pos_of_nonneg_of_pos (f : ℕ → ℝ) (a : ℝ) (h : HasSum f a)
    (hf : ∀ k, 0 ≤ f k) (k : ℕ) (hk : 0 < f k) : 0 < a := by
  have hle := h.summable.le_tsum k (fun j _ => hf j)
  rw [h.tsum_eq] at hle
  exact hk.trans_le hle

theorem poisedRationalKernel_hasSum_pos (r n m : ℕ) (a : ℝ)
    (h : HasSum (fun k : ℕ => (poisedRationalKernel r n m ((k + 1 : ℕ) : ℚ) : ℝ)) a) :
    0 < a := by
  apply hasSum_pos_of_nonneg_of_pos _ a h
    (fun k => by exact_mod_cast poisedRationalKernel_nonneg_integer r n m k) m
  exact_mod_cast poisedRationalKernel_pos_integer r n m m (by omega)

end OddZeta
