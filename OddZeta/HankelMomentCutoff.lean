import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Lemmas

namespace OddZeta

theorem bernoulli_index_cancellation_factor (p s L : ℕ)
    (hp : 1 < p) (hL : 0 < L) (hs : 3 ≤ s)
    (hd : p - 1 ∣ L) (hbound : L < (s - 1) * (p - 1)) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ s - 2 ∧ p ∣ L + j := by
  obtain ⟨k, hk⟩ := hd
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    simp [hz] at hk
    omega
  have hklt : k < s - 1 := by
    by_contra h
    have hle : s - 1 ≤ k := by omega
    have hm := Nat.mul_le_mul_left (p - 1) hle
    nlinarith [hk]
  refine ⟨k, by omega, by omega, ?_⟩
  use k
  calc
    L + k = (p - 1) * k + k := by rw [hk]
    _ = (p - 1 + 1) * k := by ring
    _ = p * k := by rw [Nat.sub_add_cancel (by omega)]

theorem bernoulli_uncancelled_index_cutoff (p s L : ℕ)
    (hp : 1 < p) (hL : 0 < L) (hs : 3 ≤ s)
    (hd : p - 1 ∣ L)
    (hbad : ∀ j : ℕ, 1 ≤ j → j ≤ s - 2 → ¬ p ∣ L + j) :
    (s - 1) * (p - 1) ≤ L := by
  by_contra h
  have hlt : L < (s - 1) * (p - 1) := by omega
  obtain ⟨j, hj, hjs, hdj⟩ :=
    bernoulli_index_cancellation_factor p s L hp hL hs hd hlt
  exact hbad j hj hjs hdj

theorem denominator_bound_of_integer_weight_raise (C M : ℕ) (x y : ℚ)
    (hC : C ≠ 0) (h : (C : ℚ) * x = (M : ℚ) * y) :
    x.den ∣ C * y.den := by
  have hc : (C : ℚ) ≠ 0 := by exact_mod_cast hC
  have hx : x = (C : ℚ)⁻¹ * ((M : ℚ) * y) := by
    rw [← h]
    simp [hc]
  have hd : x.den ∣ C * ((M : ℚ) * y).den := by
    rw [hx]
    simpa [hC] using Rat.mul_den_dvd ((C : ℚ)⁻¹) ((M : ℚ) * y)
  have hm : ((M : ℚ) * y).den ∣ y.den := by
    simpa using Rat.mul_den_dvd (M : ℚ) y
  exact hd.trans (Nat.mul_dvd_mul_left C hm)

theorem weight_seven_polynomial_moment_raise (B : ℚ) (e : ℕ) :
    30 * ((-1 : ℚ)^e * B * (2*e+3) * (2*e+4) * (2*e+5) *
      (2*e+6) * (2*e+7) / 720) =
    (2*e+6) * (2*e+7) *
      ((-1 : ℚ)^e * B * (2*e+3) * (2*e+4) * (2*e+5) / 24) := by
  ring

end OddZeta
