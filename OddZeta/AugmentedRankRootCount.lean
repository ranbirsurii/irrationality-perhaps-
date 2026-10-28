import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OddZeta

def augmentedRankRoot (n m : ℕ) : Fin (m + 1) ⊕ Fin (m + 1) → ℚ
  | Sum.inl i => (i.val : ℚ) + 1
  | Sum.inr i => -(n : ℚ) - (i.val : ℚ)

theorem augmentedRankRoot_injective (n m : ℕ) :
    Function.Injective (augmentedRankRoot n m) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hv : (i.val : ℚ) = (j.val : ℚ) := by
        simpa only [augmentedRankRoot, add_left_inj] using h
      have hij : i = j := Fin.ext (by exact_mod_cast hv)
      exact congrArg Sum.inl hij
    | inr j =>
      simp only [augmentedRankRoot] at h
      have hi : (0 : ℚ) ≤ i.val := Nat.cast_nonneg _
      have hj : (0 : ℚ) ≤ j.val := Nat.cast_nonneg _
      have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg _
      linarith
  | inr i =>
    cases y with
    | inl j =>
      simp only [augmentedRankRoot] at h
      have hi : (0 : ℚ) ≤ i.val := Nat.cast_nonneg _
      have hj : (0 : ℚ) ≤ j.val := Nat.cast_nonneg _
      have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg _
      linarith
    | inr j =>
      have hv : (i.val : ℚ) = (j.val : ℚ) := by
        simp only [augmentedRankRoot] at h
        linarith
      have hij : i = j := Fin.ext (by exact_mod_cast hv)
      exact congrArg Sum.inr hij

theorem polynomial_zero_of_augmented_rank_roots (P : Polynomial ℚ) (n m : ℕ)
    (hdegree : P.natDegree ≤ 2 * m)
    (hpositive : ∀ i : Fin (m + 1), P.eval ((i.val : ℚ) + 1) = 0)
    (hnegative : ∀ i : Fin (m + 1), P.eval (-(n : ℚ) - (i.val : ℚ)) = 0) :
    P = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (augmentedRankRoot_injective n m)
  · intro i
    cases i with
    | inl j => exact hpositive j
    | inr j => exact hnegative j
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

theorem polynomial_zero_of_reflected_rank_roots (P : Polynomial ℚ) (n m : ℕ)
    (hdegree : P.natDegree ≤ 2 * m)
    (hpositive : ∀ i : Fin (m + 1), P.eval ((i.val : ℚ) + 1) = 0)
    (hreflect : ∀ t : ℚ, P.eval (1 - (n : ℚ) - t) = P.eval t) :
    P = 0 := by
  apply polynomial_zero_of_augmented_rank_roots P n m hdegree hpositive
  intro i
  have h := hreflect ((i.val : ℚ) + 1)
  have hi : (1 : ℚ) - n - ((i.val : ℚ) + 1) = -(n : ℚ) - i.val := by ring
  rw [hi, hpositive i] at h
  exact h

theorem polynomial_zero_of_reflected_difference_chain
    (P : Polynomial ℚ) (n m s : ℕ)
    (hdegree : P.natDegree ≤ 2 * m)
    (hstart : P.eval 1 = 0)
    (hreflect : ∀ t : ℚ, P.eval (1 - (n : ℚ) - t) = P.eval t)
    (hstep : ∀ k : ℕ, 1 ≤ k → k ≤ m →
      (k : ℚ) ^ s * P.eval ((k : ℚ) + 1) -
        ((k : ℚ) + n) ^ s * P.eval (k : ℚ) = 0) :
    P = 0 := by
  have hchain : ∀ k : ℕ, k ≤ m → P.eval ((k : ℚ) + 1) = 0 := by
    intro k
    induction k with
    | zero => simpa using fun (_ : 0 ≤ m) => hstart
    | succ k ih =>
      intro hk
      have hz := ih (by omega)
      have hs := hstep (k + 1) (by omega) hk
      have hnonzero : ((k + 1 : ℕ) : ℚ) ^ s ≠ 0 := by
        apply pow_ne_zero
        exact_mod_cast Nat.succ_ne_zero k
      norm_num only [Nat.cast_add, Nat.cast_one] at hs hnonzero ⊢
      rw [hz, mul_zero, sub_zero] at hs
      exact (mul_eq_zero.mp hs).resolve_left hnonzero
  apply polynomial_zero_of_reflected_rank_roots P n m hdegree _ hreflect
  intro i
  exact hchain i.val (by omega)

end OddZeta
