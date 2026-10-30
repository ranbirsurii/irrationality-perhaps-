import OddZeta.KernelProjectorContent

namespace OddZeta

theorem scaled_row_proportionality_on_kernel {n : ℕ}
    (p c : ℤ) (a b e : ℕ) (x z X Z w : Fin n → ℤ)
    (hp : p ≠ 0)
    (hX : ∀ i, X i = p ^ a * x i)
    (hZ : ∀ i, Z i = p ^ b * z i)
    (hrow : ∀ i, p ^ e ∣ z i - c * x i)
    (hker : integralPairing X w = 0) :
    p ^ (b + e) ∣ integralPairing Z w := by
  have hscaleX : integralPairing X w = p ^ a * integralPairing x w := by
    simp [integralPairing, hX, mul_assoc, Finset.mul_sum]
  have hx : integralPairing x w = 0 := by
    rw [hscaleX] at hker
    exact (mul_eq_zero.mp hker).resolve_left (pow_ne_zero _ hp)
  have hd := dvd_integralPairing_of_entries (p ^ e)
    (fun i => z i - c * x i) w hrow
  have hdiff : integralPairing (fun i => z i - c * x i) w =
      integralPairing z w - c * integralPairing x w := by
    simp [integralPairing, sub_mul, mul_assoc, Finset.sum_sub_distrib,
      Finset.mul_sum]
  rw [hdiff, hx, mul_zero, sub_zero] at hd
  obtain ⟨k, hk⟩ := hd
  use k
  calc
    integralPairing Z w = p ^ b * integralPairing z w := by
      simp [integralPairing, hZ, mul_assoc, Finset.mul_sum]
    _ = p ^ b * (p ^ e * k) := by rw [hk]
    _ = p ^ (b + e) * k := by rw [pow_add]; ring

theorem weight_seven_row_transfer {n : ℕ}
    (p c : ℤ) (x z X Z w : Fin n → ℤ)
    (hp : p ≠ 0)
    (hX : ∀ i, X i = p ^ 4 * x i)
    (hZ : ∀ i, Z i = p * z i)
    (hrow : ∀ i, p ^ 2 ∣ z i - c * x i)
    (hker : integralPairing X w = 0) :
    p ^ 3 ∣ integralPairing Z w := by
  apply scaled_row_proportionality_on_kernel p c 4 1 2 x z X Z w hp hX
  · simpa using hZ
  · exact hrow
  · exact hker

theorem weight_seven_row_transfer_image_content {n k : ℕ}
    (p c : ℤ) (x z X Y Z : Fin n → ℤ) (v : Fin k → Fin n → ℤ)
    (hp : p ≠ 0)
    (hX : ∀ i, X i = p ^ 4 * x i)
    (hZ : ∀ i, Z i = p * z i)
    (hrow : ∀ i, p ^ 2 ∣ z i - c * x i)
    (hY : ∀ i, p ^ 3 ∣ Y i)
    (hker : ∀ j, integralPairing X (v j) = 0) :
    p ^ 3 ∣ Finset.univ.gcd (fun ij : Fin 2 × Fin k =>
      integralPairing (if ij.1 = 0 then Y else Z) (v ij.2)) := by
  apply Finset.dvd_gcd
  intro ij _
  by_cases hi : ij.1 = 0
  · simp only [hi, ite_true]
    exact dvd_integralPairing_of_entries (p ^ 3) Y (v ij.2) hY
  · simp only [hi, ite_false]
    exact weight_seven_row_transfer p c x z X Z (v ij.2) hp hX hZ hrow (hker ij.2)

theorem two_scaled_rows_congruence_on_kernel {n : ℕ}
    (p d c f A B : ℤ) (a b e : ℕ)
    (x y X V Z w : Fin n → ℤ)
    (hp : p ≠ 0)
    (hX : ∀ i, X i = p ^ a * x i)
    (hV : ∀ i, V i = p ^ b * y i)
    (hrow : ∀ i, p ^ e ∣ d * Z i + c * x i + f * y i)
    (hunit : d * A + p ^ e * B = 1)
    (hkerX : integralPairing X w = 0)
    (hkerV : integralPairing V w = 0) :
    p ^ e ∣ integralPairing Z w := by
  have hxscale : integralPairing X w = p ^ a * integralPairing x w := by
    simp [integralPairing, hX, mul_assoc, Finset.mul_sum]
  have hyscale : integralPairing V w = p ^ b * integralPairing y w := by
    simp [integralPairing, hV, mul_assoc, Finset.mul_sum]
  have hx : integralPairing x w = 0 := by
    rw [hxscale] at hkerX
    exact (mul_eq_zero.mp hkerX).resolve_left (pow_ne_zero _ hp)
  have hy : integralPairing y w = 0 := by
    rw [hyscale] at hkerV
    exact (mul_eq_zero.mp hkerV).resolve_left (pow_ne_zero _ hp)
  have hd := dvd_integralPairing_of_entries (p ^ e)
    (fun i => d * Z i + c * x i + f * y i) w hrow
  have heq : integralPairing (fun i => d * Z i + c * x i + f * y i) w =
      d * integralPairing Z w + c * integralPairing x w + f * integralPairing y w := by
    simp [integralPairing, add_mul, mul_assoc, Finset.sum_add_distrib,
      Finset.mul_sum]
  rw [heq, hx, hy, mul_zero, mul_zero, add_zero, add_zero] at hd
  obtain ⟨k, hk⟩ := hd
  use A * k + B * integralPairing Z w
  calc
    integralPairing Z w = (d * A + p ^ e * B) * integralPairing Z w := by
      rw [hunit]; ring
    _ = A * (d * integralPairing Z w) +
        p ^ e * (B * integralPairing Z w) := by ring
    _ = p ^ e * (A * k + B * integralPairing Z w) := by rw [hk]; ring

theorem coarse_weight_seven_row_relation :
    (174 * 306 + 191 * (-196) + 247 * (-64) : ℤ) = 0 ∧
    (174 * (-98) + 191 * 66 + 247 * 18 : ℤ) = 0 := by
  decide

end OddZeta
