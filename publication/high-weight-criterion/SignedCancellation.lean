import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OddZeta

theorem signed_combination_bound {n : ℕ} (w f : Fin n → ℝ) (S : ℝ)
    (hf : ∀ i, |f i| ≤ S) :
    |∑ i, w i * f i| ≤ (∑ i, |w i|) * S := by
  calc
    |∑ i, w i * f i| ≤ ∑ i, |w i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |w i| * |f i| := by simp only [abs_mul]
    _ ≤ ∑ i, |w i| * S :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _))
    _ = (∑ i, |w i|) * S := (Finset.sum_mul _ _ _).symm

theorem two_forms_not_both_zero (α a b c d : ℝ)
    (hdet : a * d - b * c ≠ 0) :
    a * α + c ≠ 0 ∨ b * α + d ≠ 0 := by
  by_cases ha : a * α + c = 0
  · right
    intro hb
    apply hdet
    calc
      a * d - b * c = a * (b * α + d) - b * (a * α + c) := by ring
      _ = 0 := by rw [ha, hb]; ring
  · exact Or.inl ha

theorem target_eliminating_combination (α a b c d : ℝ) :
    a * (b * α + d) - b * (a * α + c) = a * d - b * c := by
  ring

theorem cofactor_determinant_square_divisor (g a b c d : ℤ)
    (ha : g ∣ a) (hb : g ∣ b) (hc : g ∣ c) (hd : g ∣ d) :
    g ^ 2 ∣ a * d - b * c := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨d', rfl⟩ := hd
  refine ⟨a' * d' - b' * c', ?_⟩
  ring

theorem square_divisor_le_abs (g δ : ℤ) (hδ : δ ≠ 0) (hdiv : g ^ 2 ∣ δ) :
    (g : ℝ) ^ 2 ≤ |(δ : ℝ)| := by
  obtain ⟨k, hk⟩ := hdiv
  have hkne : k ≠ 0 := by
    intro hz
    apply hδ
    simp [hk, hz]
  have hkabs : (1 : ℤ) ≤ |k| := by
    have h := abs_pos.mpr hkne
    omega
  have hkR : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkabs
  rw [hk, Int.cast_mul, Int.cast_pow, abs_mul, abs_of_nonneg (sq_nonneg _)]
  simpa using mul_le_mul_of_nonneg_left hkR (sq_nonneg (g : ℝ))

theorem cofactor_content_lower_bound (g δ : ℤ) (D U S : ℝ)
    (hδ : δ ≠ 0) (hdiv : g ^ 2 ∣ δ)
    (hbound : |(δ : ℝ)| ≤ D * U * S) :
    (g : ℝ) ^ 2 ≤ D * U * S :=
  (square_divisor_le_abs g δ hδ hdiv).trans hbound

theorem cofactor_strict_saving_impossible (g δ : ℤ) (D U S : ℝ)
    (hδ : δ ≠ 0) (hdiv : g ^ 2 ∣ δ)
    (hbound : |(δ : ℝ)| ≤ D * U * S)
    (hsaving : D * U * S < (g : ℝ) ^ 2) : False := by
  have h := cofactor_content_lower_bound g δ D U S hδ hdiv hbound
  linarith

end OddZeta

#print axioms OddZeta.signed_combination_bound
#print axioms OddZeta.two_forms_not_both_zero
#print axioms OddZeta.cofactor_strict_saving_impossible
