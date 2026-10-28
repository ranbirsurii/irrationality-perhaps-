import OddZeta.GramSpectralBounds
import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp

namespace OddZeta

theorem psd_gram_eigenmax_bounds (A B C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hBC : B ^ 2 ≤ A * C) :
    A ≤ gramEigenMax A B C ∧ C ≤ gramEigenMax A B C ∧
      gramEigenMax A B C ≤ A + C := by
  have hlower : |C - A| ≤ Real.sqrt ((C - A) ^ 2 + 4 * B ^ 2) := by
    calc
      |C - A| = Real.sqrt ((C - A) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg B])
  have hupper : Real.sqrt ((C - A) ^ 2 + 4 * B ^ 2) ≤ A + C := by
    calc
      _ ≤ Real.sqrt ((A + C) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = A + C := Real.sqrt_sq (add_nonneg hA hC)
  have hl := le_abs_self (C - A)
  have hr := neg_le_abs (C - A)
  unfold gramEigenMax
  constructor
  · linarith
  constructor <;> linarith

noncomputable def primitivePairSpectralCost (A B C h k : ℝ) : ℝ :=
  gramEigenMax (A / h ^ 2) (B / (h * k)) (C / k ^ 2)

theorem individually_scaled_gram_psd (A B C h k : ℝ)
    (hBC : B ^ 2 ≤ A * C) (hh : 0 < h) (hk : 0 < k) :
    (B / (h * k)) ^ 2 ≤ (A / h ^ 2) * (C / k ^ 2) := by
  have hidentity : (A / h ^ 2) * (C / k ^ 2) - (B / (h * k)) ^ 2 =
      (A * C - B ^ 2) / (h * k) ^ 2 := by
    field_simp
  have hnonneg : 0 ≤ (A * C - B ^ 2) / (h * k) ^ 2 :=
    div_nonneg (sub_nonneg.mpr hBC) (sq_nonneg _)
  linarith

theorem primitive_pair_spectral_bounds (A B C h k : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hBC : B ^ 2 ≤ A * C)
    (hh : 0 < h) (hk : 0 < k) :
    A / h ^ 2 ≤ primitivePairSpectralCost A B C h k ∧
      C / k ^ 2 ≤ primitivePairSpectralCost A B C h k ∧
      primitivePairSpectralCost A B C h k ≤ A / h ^ 2 + C / k ^ 2 := by
  exact psd_gram_eigenmax_bounds _ _ _ (by positivity) (by positivity)
    (individually_scaled_gram_psd A B C h k hBC hh hk)

theorem primitive_pair_trace_le_common_content (A C h k Γ : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hΓ : 0 < Γ)
    (hh : Γ ≤ h) (hk : Γ ≤ k) :
    A / h ^ 2 + C / k ^ 2 ≤ (A + C) / Γ ^ 2 := by
  have hhpos : 0 < h := hΓ.trans_le hh
  have hkpos : 0 < k := hΓ.trans_le hk
  have hhsq : Γ ^ 2 ≤ h ^ 2 := by nlinarith
  have hksq : Γ ^ 2 ≤ k ^ 2 := by nlinarith
  calc
    _ ≤ A / Γ ^ 2 + C / Γ ^ 2 := add_le_add
      (div_le_div_of_nonneg_left hA (sq_pos_of_pos hΓ) hhsq)
      (div_le_div_of_nonneg_left hC (sq_pos_of_pos hΓ) hksq)
    _ = _ := (add_div _ _ _).symm

theorem primitive_pair_form_bounds (A B C h k P La Lb : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hBC : B ^ 2 ≤ A * C)
    (hh : 0 < h) (hk : 0 < k) (hP : 0 ≤ P)
    (ha : |La| ≤ P * Real.sqrt A / h)
    (hb : |Lb| ≤ P * Real.sqrt C / k) :
    |La| ≤ P * Real.sqrt (primitivePairSpectralCost A B C h k) ∧
      |Lb| ≤ P * Real.sqrt (primitivePairSpectralCost A B C h k) := by
  have hμ := primitive_pair_spectral_bounds A B C h k hA hC hBC hh hk
  have hsa : Real.sqrt (A / h ^ 2) = Real.sqrt A / h := by
    rw [Real.sqrt_div hA, Real.sqrt_sq hh.le]
  have hsc : Real.sqrt (C / k ^ 2) = Real.sqrt C / k := by
    rw [Real.sqrt_div hC, Real.sqrt_sq hk.le]
  constructor
  · calc
      |La| ≤ P * Real.sqrt A / h := ha
      _ = P * Real.sqrt (A / h ^ 2) := by rw [hsa, mul_div_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hμ.1) hP
  · calc
      |Lb| ≤ P * Real.sqrt C / k := hb
      _ = P * Real.sqrt (C / k ^ 2) := by rw [hsc, mul_div_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hμ.2.1) hP

theorem integral_normalized_form (a c h : ℤ) (α : ℝ)
    (ha : h ∣ a) (hc : h ∣ c) (hh : (h : ℝ) ≠ 0) :
    ((a / h : ℤ) : ℝ) * α + ((c / h : ℤ) : ℝ) =
      ((a : ℝ) * α + (c : ℝ)) / (h : ℝ) := by
  rw [Int.cast_div ha hh, Int.cast_div hc hh]
  ring

theorem integral_normalized_pair_nonvanishing (a b c d h k : ℤ) (α : ℝ)
    (ha : h ∣ a) (hc : h ∣ c) (hb : k ∣ b) (hd : k ∣ d)
    (hh : (h : ℝ) ≠ 0) (hk : (k : ℝ) ≠ 0)
    (hdet : a * d - b * c ≠ 0) :
    ((a / h : ℤ) : ℝ) * α + ((c / h : ℤ) : ℝ) ≠ 0 ∨
      ((b / k : ℤ) : ℝ) * α + ((d / k : ℤ) : ℝ) ≠ 0 := by
  rw [integral_normalized_form a c h α ha hc hh,
    integral_normalized_form b d k α hb hd hk]
  by_cases hfirst : (a : ℝ) * α + (c : ℝ) = 0
  · right
    apply div_ne_zero _ hk
    intro hsecond
    have hreal : (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ) ≠ 0 := by
      exact_mod_cast hdet
    apply hreal
    calc
      _ = (a : ℝ) * ((b : ℝ) * α + (d : ℝ)) -
          (b : ℝ) * ((a : ℝ) * α + (c : ℝ)) := by ring
      _ = 0 := by rw [hfirst, hsecond]; ring
  · exact Or.inl (div_ne_zero hfirst hh)

theorem pair_gcd_positive_of_determinant (a b c d : ℤ)
    (hdet : a * d - b * c ≠ 0) : 0 < Int.gcd a c ∧ 0 < Int.gcd b d := by
  constructor
  · by_contra h
    have hz : Int.gcd a c = 0 := by omega
    obtain ⟨ha, hc⟩ := Int.gcd_eq_zero_iff.mp hz
    exact hdet (by simp [ha, hc])
  · by_contra h
    have hz : Int.gcd b d = 0 := by omega
    obtain ⟨hb, hd⟩ := Int.gcd_eq_zero_iff.mp hz
    exact hdet (by simp [hb, hd])

theorem primitive_gcd_pair_nonvanishing (a b c d : ℤ) (α : ℝ)
    (hdet : a * d - b * c ≠ 0) :
    (((a / Int.gcd a c : ℤ) : ℝ) * α + ((c / Int.gcd a c : ℤ) : ℝ) ≠ 0 ∨
      ((b / Int.gcd b d : ℤ) : ℝ) * α + ((d / Int.gcd b d : ℤ) : ℝ) ≠ 0) ∧
      Int.gcd (a / Int.gcd a c) (c / Int.gcd a c) = 1 ∧
      Int.gcd (b / Int.gcd b d) (d / Int.gcd b d) = 1 := by
  have hpos := pair_gcd_positive_of_determinant a b c d hdet
  have hh : (0 : ℝ) < ((Int.gcd a c : ℤ) : ℝ) := by exact_mod_cast hpos.1
  have hk : (0 : ℝ) < ((Int.gcd b d : ℤ) : ℝ) := by exact_mod_cast hpos.2
  exact ⟨integral_normalized_pair_nonvanishing a b c d (Int.gcd a c)
    (Int.gcd b d) α (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
    (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _) (ne_of_gt hh) (ne_of_gt hk) hdet,
    Int.gcd_div_gcd_div_gcd hpos.1, Int.gcd_div_gcd_div_gcd hpos.2⟩

end OddZeta
