import OddZeta.OddHankelArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic

namespace OddZeta

theorem endpoint_log_bounds (x : ℝ) (hx : 0 < x) :
    1 - x ≤ -Real.log x ∧ x * (-Real.log x) ≤ 1 - x := by
  have hleft := Real.log_le_sub_one_of_pos hx
  have hright := Real.one_sub_inv_le_log_of_pos hx
  have hi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  constructor
  · linarith
  · have hscaled := mul_le_mul_of_nonneg_left hright hx.le
    nlinarith

theorem endpoint_log_power_bounds (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k ≤ (-Real.log x) ^ k ∧
      (x * (-Real.log x)) ^ k ≤ (1 - x) ^ k := by
  have h := endpoint_log_bounds x hx
  have hxnonneg : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hlognonneg : 0 ≤ -Real.log x := hxnonneg.trans h.1
  exact ⟨pow_le_pow_left₀ hxnonneg h.1 k,
    pow_le_pow_left₀ (mul_nonneg hx.le hlognonneg) h.2 k⟩

noncomputable def endpointMomentWeight (r a : ℕ) (x : ℝ) : ℝ :=
  x ^ a * (-Real.log x) ^ (2 * r) /
    (((2 * r).factorial : ℝ) * (1 - x))

noncomputable def endpointJacobiWeight (r a : ℕ) (x : ℝ) : ℝ :=
  x ^ a * (1 - x) ^ (2 * r - 1) / ((2 * r).factorial : ℝ)

theorem endpoint_weight_sandwich (r a : ℕ) (hr : 0 < r)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    endpointJacobiWeight r a x ≤ endpointMomentWeight r a x ∧
      x ^ (2 * r) * endpointMomentWeight r a x ≤ endpointJacobiWeight r a x := by
  have hp := endpoint_log_power_bounds x hx hx1.le (2 * r)
  have hf : (0 : ℝ) < ((2 * r).factorial : ℝ) := by positivity
  have hd : (0 : ℝ) < ((2 * r).factorial : ℝ) * (1 - x) :=
    mul_pos hf (sub_pos.mpr hx1)
  have hpower : (1 - x) ^ (2 * r) = (1 - x) ^ (2 * r - 1) * (1 - x) := by
    have hi : 2 * r = (2 * r - 1) + 1 := by omega
    conv_lhs => rw [hi, pow_succ]
  have hq : endpointJacobiWeight r a x *
      (((2 * r).factorial : ℝ) * (1 - x)) = x ^ a * (1 - x) ^ (2 * r) := by
    unfold endpointJacobiWeight
    rw [hpower]
    field_simp
  constructor
  · unfold endpointMomentWeight
    apply (le_div_iff₀ hd).mpr
    rw [hq]
    exact mul_le_mul_of_nonneg_left hp.1 (pow_nonneg hx.le a)
  · unfold endpointMomentWeight
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    rw [hq]
    calc
      x ^ (2 * r) * (x ^ a * (-Real.log x) ^ (2 * r)) =
          x ^ a * (x * (-Real.log x)) ^ (2 * r) := by rw [mul_pow]; ring
      _ ≤ x ^ a * (1 - x) ^ (2 * r) :=
        mul_le_mul_of_nonneg_left hp.2 (pow_nonneg hx.le a)

theorem endpoint_ascFactorial_bounds (n k : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ k ≤ (n.ascFactorial k : ℝ) ∧
      (n.ascFactorial k : ℝ) ≤ ((n + k - 1 : ℕ) : ℝ) ^ k := by
  constructor
  · exact_mod_cast Nat.pow_succ_le_ascFactorial n k
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have h := Nat.ascFactorial_le_pow_add m k
    have hi : m + 1 + k - 1 = m + k := by omega
    rw [hi]
    exact_mod_cast h

def endpointJacobiBound (r n a : ℕ) : ℚ :=
  ((2 * r - 1).factorial : ℚ) /
    ((n.ascFactorial (2 * r) : ℚ) * ((n + a).ascFactorial (2 * r) : ℚ))

theorem endpointJacobiBound_pos (r n a : ℕ) (hn : 0 < n) :
    0 < endpointJacobiBound r n a := by
  unfold endpointJacobiBound
  have hfirst : 0 < n.ascFactorial (2 * r) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact Nat.ascFactorial_pos m _
  have hsecond : 0 < (n + a).ascFactorial (2 * r) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n + a ≠ 0 by omega)
    rw [hm]
    exact Nat.ascFactorial_pos m _
  exact div_pos (by positivity) (mul_pos (by exact_mod_cast hfirst)
    (by exact_mod_cast hsecond))

theorem endpointJacobiBound_nat_lower (r n a : ℕ) (hn : 0 < n) :
    ((2 * r - 1).factorial : ℝ) /
        (((n + 2 * r - 1 : ℕ) : ℝ) ^ (2 * r) *
          ((n + a + 2 * r - 1 : ℕ) : ℝ) ^ (2 * r)) ≤
      (endpointJacobiBound r n a : ℝ) := by
  have h1 := (endpoint_ascFactorial_bounds n (2 * r) hn).2
  have h2 := (endpoint_ascFactorial_bounds (n + a) (2 * r) (by omega)).2
  have hpos1 : (0 : ℝ) < (n.ascFactorial (2 * r) : ℝ) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact_mod_cast Nat.ascFactorial_pos m (2 * r)
  have hpos2 : (0 : ℝ) < ((n + a).ascFactorial (2 * r) : ℝ) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n + a ≠ 0 by omega)
    rw [hm]
    exact_mod_cast Nat.ascFactorial_pos m (2 * r)
  unfold endpointJacobiBound
  push_cast
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos hpos1 hpos2)
    (mul_le_mul h1 h2 hpos2.le (hpos1.le.trans h1))

end OddZeta
