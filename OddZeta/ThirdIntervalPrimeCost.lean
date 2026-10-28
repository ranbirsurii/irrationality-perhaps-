import OddZeta.HarmonicDenominatorGrowth

namespace OddZeta

theorem scaled_reciprocal_prime_den (p s b d : ℕ) (q : ℚ) (hp : p.Prime)
    (hb : ¬ p ∣ b) (h : q * ((d : ℚ) / b) = (1 : ℚ) / (p : ℚ) ^ s) :
    p ^ s ∣ q.den := by
  have hd : ((d : ℚ) / b).den ∣ b := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [Rat.divInt_eq_div, Int.cast_natCast] using Rat.den_dvd (d : ℤ) (b : ℤ)
  have hv := Rat.mul_den_dvd q ((d : ℚ) / b)
  rw [h, reciprocal_power_den p s hp.pos] at hv
  exact ((hp.coprime_iff_not_dvd.mpr hb).pow_left s).dvd_of_dvd_mul_right
    (hv.trans (Nat.mul_dvd_mul_left q.den hd))

theorem upper_third_prime_not_dvd_other (a p j : ℕ) (hp : p.Prime)
    (hthird : a < 3 * p) (hj : j < a)
    (hne : j ≠ p - 1) (hne2 : j ≠ 2 * p - 1) : ¬ p ∣ j + 1 := by
  rintro ⟨k, hk⟩
  have hlt : p * k < p * 3 := by omega
  have hklt : k < 3 := (Nat.mul_lt_mul_left hp.pos).mp hlt
  have hk0 : k ≠ 0 := by intro hz; simp [hz] at hk
  have hk1 : k ≠ 1 := by intro hz; simp only [hz, mul_one] at hk; omega
  have hk2 : k ≠ 2 := by intro hz; simp only [hz] at hk; omega
  omega

theorem upper_third_prime_power_dvd_harmonic_den (s a p : ℕ)
    (hp : p.Prime) (hpa : p ≤ a) (hthird : a < 3 * p)
    (hbad : ¬ p ∣ 2 ^ s + 1) : p ^ s ∣ (harmonicPower s a).den := by
  classical
  by_cases hhalf : a < 2 * p
  · exact upper_half_prime_power_dvd_harmonic_den s a p hp hpa hhalf
  have hp2a : 2 * p ≤ a := by omega
  let S := ((Finset.range a).erase (p - 1)).erase (2 * p - 1)
  let R : ℚ := ∑ j ∈ S, 1 / ((j + 1 : ℕ) : ℚ) ^ s
  let q : ℚ := (1 : ℚ) / (p : ℚ) ^ s + 1 / ((2 * p : ℕ) : ℚ) ^ s
  have hpmem : p - 1 ∈ Finset.range a := Finset.mem_range.mpr (by have := hp.pos; omega)
  have hp2mem : 2 * p - 1 ∈ (Finset.range a).erase (p - 1) := by
    apply Finset.mem_erase.mpr
    exact ⟨by have := hp.pos; omega, Finset.mem_range.mpr (by have := hp.pos; omega)⟩
  have hR : ¬ p ∣ R.den := by
    apply prime_not_dvd_sum_den p hp S _
    intro j hj
    have hj2 := Finset.mem_erase.mp hj
    have hj1 := Finset.mem_erase.mp hj2.2
    have hnot := upper_third_prime_not_dvd_other a p j hp hthird
      (Finset.mem_range.mp hj1.2) hj1.1 hj2.1
    rw [reciprocal_power_den (j + 1) s (by omega)]
    exact fun h => hnot (hp.dvd_of_dvd_pow h)
  have hsplit : harmonicPower s a = q + R := by
    have h1 := Finset.add_sum_erase (Finset.range a)
      (fun j => (1 : ℚ) / ((j + 1 : ℕ) : ℚ) ^ s) hpmem
    have h2 := Finset.add_sum_erase ((Finset.range a).erase (p - 1))
      (fun j => (1 : ℚ) / ((j + 1 : ℕ) : ℚ) ^ s) hp2mem
    unfold harmonicPower
    rw [← h1, ← h2]
    simp only [Nat.sub_add_cancel hp.one_le,
      Nat.sub_add_cancel (show 1 ≤ 2 * p by have := hp.pos; omega)]
    change _ = q + R
    dsimp [q, R, S]
    ring
  have hscale : q * (((2 ^ s : ℕ) : ℚ) / ((2 ^ s + 1 : ℕ) : ℚ)) =
      (1 : ℚ) / (p : ℚ) ^ s := by
    dsimp [q]
    push_cast
    rw [mul_pow]
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hC : (2 : ℚ) ^ s + 1 ≠ 0 := by positivity
    field_simp
  have hq := scaled_reciprocal_prime_den p s (2 ^ s + 1) (2 ^ s) q hp hbad hscale
  have hsub : harmonicPower s a - R = q := by rw [hsplit]; ring
  have hdvd := Rat.sub_den_dvd (harmonicPower s a) R
  rw [hsub] at hdvd
  exact ((hp.coprime_iff_not_dvd.mpr hR).pow_left s).dvd_of_dvd_mul_right
    (hq.trans hdvd)

def upperThirdPrimes (s a : ℕ) : Finset ℕ :=
  (Finset.range (a + 1)).filter (fun p => p.Prime ∧ a < 3 * p ∧ ¬ p ∣ 2 ^ s + 1)

def upperThirdPrimeProduct (s a : ℕ) : ℕ := ∏ p ∈ upperThirdPrimes s a, p

theorem upperThirdPrimeProduct_pow_dvd_harmonic_den (s a : ℕ) :
    upperThirdPrimeProduct s a ^ s ∣ (harmonicPower s a).den := by
  classical
  unfold upperThirdPrimeProduct
  rw [← Finset.prod_pow]
  apply nat_coprime_finset_prod_dvd
  · intro p hp q hq hne
    have hp' := (Finset.mem_filter.mp hp).2.1
    have hq' := (Finset.mem_filter.mp hq).2.1
    exact ((Nat.coprime_primes hp' hq').mpr hne).pow s s
  · intro p hp
    have h := Finset.mem_filter.mp hp
    exact upper_third_prime_power_dvd_harmonic_den s a p h.2.1
      (by have := Finset.mem_range.mp h.1; omega) h.2.2.1 h.2.2.2

theorem shifted_harmonic_third_prime_cost (s a : ℕ) (p c : ℤ) (u m : ℕ)
    (h : harmonicPower s a = (p : ℚ) / u + (c : ℚ) / m) :
    upperThirdPrimeProduct s a ^ s ∣ u * m :=
  (upperThirdPrimeProduct_pow_dvd_harmonic_den s a).trans
    (rational_sum_den_dvd _ p c u m h)

theorem shifted_harmonic_third_height_lower (s a : ℕ) (p c : ℤ) (u m D : ℕ)
    (hu : 0 < u) (hm : 0 < m) (hmD : m ≤ D)
    (h : harmonicPower s a = (p : ℚ) / u + (c : ℚ) / m) :
    upperThirdPrimeProduct s a ^ s ≤ u * D := by
  exact (Nat.le_of_dvd (Nat.mul_pos hu hm)
    (shifted_harmonic_third_prime_cost s a p c u m h)).trans
      (Nat.mul_le_mul_left u hmD)

end OddZeta
