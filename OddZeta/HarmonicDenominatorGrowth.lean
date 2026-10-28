import OddZeta.OddHankelArithmetic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.GCD.BigOperators

namespace OddZeta

theorem nat_coprime_finset_prod_dvd {ι : Type*} (S : Finset ι) (f : ι → ℕ) (b : ℕ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (f i).Coprime (f j))
    (hf : ∀ i ∈ S, f i ∣ b) : (∏ i ∈ S, f i) ∣ b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      have hc : (f i).Coprime (∏ j ∈ S, f j) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro j hj
        exact hpair i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj)
          (by intro heq; subst j; exact hi hj)
      exact hc.mul_dvd_of_dvd_of_dvd (hf i (Finset.mem_insert_self i S))
        (ih (fun j hj k hk hne => hpair j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hne)
          (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem prime_not_dvd_sum_den {ι : Type*} (p : ℕ) (hp : p.Prime)
    (S : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ S, ¬ p ∣ (f i).den) : ¬ p ∣ (∑ i ∈ S, f i).den := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      intro h
      rcases hp.dvd_mul.mp (h.trans (Rat.add_den_dvd _ _)) with h | h
      · exact hf i (Finset.mem_insert_self i S) h
      · exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) h

theorem upper_half_prime_not_dvd_other (a p j : ℕ) (hp : p.Prime)
    (hhalf : a < 2 * p) (hj : j < a) (hne : j ≠ p - 1) : ¬ p ∣ j + 1 := by
  rintro ⟨k, hk⟩
  have hlt : p * k < p * 2 := by omega
  have hklt : k < 2 := (Nat.mul_lt_mul_left hp.pos).mp hlt
  have hk0 : k ≠ 0 := by intro hz; simp [hz] at hk
  have hk1 : k = 1 := by omega
  simp only [hk1, mul_one] at hk
  omega

theorem reciprocal_power_den (k s : ℕ) (hk : 0 < k) :
    ((1 : ℚ) / (k : ℚ) ^ s).den = k ^ s := by
  rw [← Nat.cast_pow, one_div, Rat.inv_natCast_den_of_pos (pow_pos hk s)]

theorem upper_half_prime_power_dvd_harmonic_den (s a p : ℕ)
    (hp : p.Prime) (hpa : p ≤ a) (hhalf : a < 2 * p) :
    p ^ s ∣ (harmonicPower s a).den := by
  classical
  let S := (Finset.range a).erase (p - 1)
  let R : ℚ := ∑ j ∈ S, 1 / ((j + 1 : ℕ) : ℚ) ^ s
  have hpmem : p - 1 ∈ Finset.range a := Finset.mem_range.mpr (by have := hp.pos; omega)
  have hR : ¬ p ∣ R.den := by
    apply prime_not_dvd_sum_den p hp S _
    intro j hj
    have hj' := Finset.mem_erase.mp hj
    have hnot := upper_half_prime_not_dvd_other a p j hp hhalf
      (Finset.mem_range.mp hj'.2) hj'.1
    rw [reciprocal_power_den (j + 1) s (by omega)]
    exact fun h => hnot (hp.dvd_of_dvd_pow h)
  have hsplit : harmonicPower s a = (1 : ℚ) / (p : ℚ) ^ s + R := by
    have h := Finset.add_sum_erase (Finset.range a)
      (fun j => (1 : ℚ) / ((j + 1 : ℕ) : ℚ) ^ s) hpmem
    simpa [harmonicPower, R, S, Nat.sub_add_cancel hp.one_le] using h.symm
  have hsub : harmonicPower s a - R = (1 : ℚ) / (p : ℚ) ^ s := by
    rw [hsplit]
    ring
  have hdvd := Rat.sub_den_dvd (harmonicPower s a) R
  rw [hsub, reciprocal_power_den p s hp.pos] at hdvd
  exact ((hp.coprime_iff_not_dvd.mpr hR).pow_left s).dvd_of_dvd_mul_right hdvd

def upperHalfPrimes (a : ℕ) : Finset ℕ :=
  (Finset.range (a + 1)).filter (fun p => p.Prime ∧ a < 2 * p)

def upperHalfPrimeProduct (a : ℕ) : ℕ := ∏ p ∈ upperHalfPrimes a, p

theorem upperHalfPrimeProduct_pow_dvd_harmonic_den (s a : ℕ) :
    upperHalfPrimeProduct a ^ s ∣ (harmonicPower s a).den := by
  classical
  unfold upperHalfPrimeProduct
  rw [← Finset.prod_pow]
  apply nat_coprime_finset_prod_dvd
  · intro p hp q hq hne
    have hp' := (Finset.mem_filter.mp hp).2.1
    have hq' := (Finset.mem_filter.mp hq).2.1
    exact ((Nat.coprime_primes hp' hq').mpr hne).pow s s
  · intro p hp
    have h := Finset.mem_filter.mp hp
    exact upper_half_prime_power_dvd_harmonic_den s a p h.2.1
      (by have := Finset.mem_range.mp h.1; omega) h.2.2

theorem rational_sum_den_dvd (q : ℚ) (p c : ℤ) (u m : ℕ)
    (h : q = (p : ℚ) / u + (c : ℚ) / m) : q.den ∣ u * m := by
  rw [h]
  exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul
    (by exact_mod_cast (Rat.den_dvd p u)) (by exact_mod_cast (Rat.den_dvd c m)))

theorem shifted_harmonic_prime_cost (s a : ℕ) (p c : ℤ) (u m : ℕ)
    (h : harmonicPower s a = (p : ℚ) / u + (c : ℚ) / m) :
    upperHalfPrimeProduct a ^ s ∣ u * m :=
  (upperHalfPrimeProduct_pow_dvd_harmonic_den s a).trans
    (rational_sum_den_dvd _ p c u m h)

theorem shifted_harmonic_height_lower (s a : ℕ) (p c : ℤ) (u m D : ℕ)
    (hu : 0 < u) (hm : 0 < m) (hmD : m ≤ D)
    (h : harmonicPower s a = (p : ℚ) / u + (c : ℚ) / m) :
    upperHalfPrimeProduct a ^ s ≤ u * D := by
  exact (Nat.le_of_dvd (Nat.mul_pos hu hm)
    (shifted_harmonic_prime_cost s a p c u m h)).trans
      (Nat.mul_le_mul_left u hmD)

end OddZeta
