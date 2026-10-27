import OddZeta.AperyDeformation

namespace OddZeta

set_option maxRecDepth 10000

def aperyTelescoperK (n z : ℚ) : ℚ := 6 * n ^ 4 + 4 * n ^ 2 * z + z ^ 2

def aperyTelescoperPlus (n z : ℚ) : ℚ :=
  -(n + 1) * ((n + 1) ^ 2 + z) ^ 2 * ((n + 1) ^ 2 + 4 * z) *
    aperyTelescoperK n z

def aperyTelescoperMinus (n z : ℚ) : ℚ :=
  -n ^ 3 * (n ^ 2 + z) ^ 2 * aperyTelescoperK (n + 1) z

def aperyTelescoperMiddle (n z : ℚ) : ℚ :=
  let u := n * (n + 1);
  (2 * n + 1) *
    (6 * u ^ 4 * (5 + 17 * u) +
      4 * u ^ 2 * (5 + 27 * u + 47 * u ^ 2) * z +
      (5 + 37 * u + 126 * u ^ 2 + 163 * u ^ 3) * z ^ 2 +
      4 * (3 + 14 * u + 19 * u ^ 2) * z ^ 3 +
      (9 + 19 * u) * z ^ 4 + 2 * z ^ 5)

def aperyTelescoperCert0 (n z : ℚ) : ℚ :=
  let u := n * (n + 1);
  -24 * u ^ 4 * (1 + 4 * u) -
    2 * u ^ 2 * (8 + 48 * u + 77 * u ^ 2) * z -
    4 * (1 + 8 * u + 25 * u ^ 2 + 29 * u ^ 3) * z ^ 2 +
    (-7 - 33 * u - 39 * u ^ 2) * z ^ 3 -
    5 * (1 + 2 * u) * z ^ 4 - 2 * z ^ 5 +
    n * (-48 * u ^ 4 * (1 + 4 * u) -
      32 * u ^ 2 * (1 + 6 * u + 10 * u ^ 2) * z -
      2 * (4 + 32 * u + 104 * u ^ 2 + 125 * u ^ 3) * z ^ 2 -
      2 * (8 + 41 * u + 55 * u ^ 2) * z ^ 3 +
      (-11 - 27 * u) * z ^ 4 - 3 * z ^ 5)

def aperyTelescoperCert1 (n z : ℚ) : ℚ :=
  let u := n * (n + 1);
  -24 * u ^ 4 - 16 * u ^ 2 * (1 + 2 * u + 3 * u ^ 2) * z -
    4 * (1 + 4 * u + 9 * u ^ 2 + 8 * u ^ 3) * z ^ 2 +
    2 * (-3 - 4 * u + 2 * u ^ 2) * z ^ 3 + 8 * u * z ^ 4 + 2 * z ^ 5 +
    n * (-48 * u ^ 4 - 32 * u ^ 2 * (1 + 2 * u) * z -
      8 * (1 + 4 * u + 5 * u ^ 2) * z ^ 2 -
      16 * (1 + 2 * u) * z ^ 3 - 8 * z ^ 4)

def aperyTelescoperCert2 (n z : ℚ) : ℚ :=
  let u := n * (n + 1);
  48 * u ^ 4 + 2 * u ^ 2 * (16 + 25 * u) * z +
    2 * (4 + 15 * u + 21 * u ^ 2) * z ^ 2 +
    (13 + 27 * u) * z ^ 3 + 5 * z ^ 4 +
    n * (96 * u ^ 4 + 32 * u ^ 2 * (2 + 5 * u) * z +
      4 * (4 + 21 * u + 29 * u ^ 2) * z ^ 2 +
      8 * (2 + 5 * u) * z ^ 3 + 6 * z ^ 4)

def aperyTelescoperCertificate (n z t : ℚ) : ℚ :=
  aperyTelescoperCert0 n z + aperyTelescoperCert1 n z * t +
    aperyTelescoperCert2 n z * t ^ 2

set_option maxHeartbeats 800000 in
theorem aperyDeformedTelescoper_polynomial_identity (n z t : ℚ) :
    aperyTelescoperPlus n z * (t - n - 1) ^ 2 * (t - n) ^ 2 +
      aperyTelescoperMiddle n z * (t - n) ^ 2 * ((t + n + 1) ^ 2 + z) +
      aperyTelescoperMinus n z * ((t + n) ^ 2 + z) *
        ((t + n + 1) ^ 2 + z) =
    t ^ 2 * (t ^ 2 + z) * aperyTelescoperCertificate n z (t + 1) -
      (t - n) ^ 2 * ((t + n + 1) ^ 2 + z) * aperyTelescoperCertificate n z t := by
  unfold aperyTelescoperPlus aperyTelescoperMiddle aperyTelescoperMinus
    aperyTelescoperK aperyTelescoperCertificate aperyTelescoperCert0
    aperyTelescoperCert1 aperyTelescoperCert2
  dsimp
  ring

theorem aperyNumerator_diagonal (n : ℕ) (t : ℚ) :
    aperyNumerator (n + 1) (t + 1) = t * aperyNumerator n t := by
  induction n with
  | zero => simp [aperyNumerator]
  | succ n ih =>
      rw [aperyNumerator_succ, ih, aperyNumerator_succ]
      push_cast
      ring

theorem aperyQuadraticDenominator_diagonal (n : ℕ) (t z : ℚ) :
    aperyQuadraticDenominator (n + 1) (t + 1) z * (t ^ 2 + z) =
      aperyQuadraticDenominator n t z *
        ((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z) *
          ((t + ((n + 2 : ℕ) : ℚ)) ^ 2 + z) := by
  induction n with
  | zero =>
      simp [aperyQuadraticDenominator, Finset.prod_range_succ]
      ring
  | succ n ih =>
      rw [aperyQuadraticDenominator_succ (n + 1) (t + 1) z,
        aperyQuadraticDenominator_succ n t z]
      calc
        _ = (aperyQuadraticDenominator (n + 1) (t + 1) z * (t ^ 2 + z)) *
            ((t + ((n + 3 : ℕ) : ℚ)) ^ 2 + z) := by push_cast; ring
        _ = _ := by rw [ih]

theorem aperyQuadraticDenominator_ne_zero (n : ℕ) (t z : ℚ)
    (hquad : ∀ j : ℕ, (t + (j : ℚ)) ^ 2 + z ≠ 0) :
    aperyQuadraticDenominator n t z ≠ 0 := by
  unfold aperyQuadraticDenominator
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => hquad j)

theorem aperyR_diagonal_cleared (n : ℕ) (t z : ℚ)
    (hshift : ∀ j : ℕ, t + (j : ℚ) ≠ 0)
    (hquad : ∀ j : ℕ, (t + (j : ℚ)) ^ 2 + z ≠ 0) :
    aperyR (n + 1) (t + 1) z *
        ((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z) *
          ((t + ((n + 2 : ℕ) : ℚ)) ^ 2 + z) =
      t ^ 2 * (t ^ 2 + z) * aperyR n t z := by
  have hshift' (j : ℕ) : t + 1 + (j : ℚ) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      using hshift (j + 1)
  have hquad' (j : ℕ) : (t + 1 + (j : ℚ)) ^ 2 + z ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      using hquad (j + 1)
  have hR0 := aperyR_quadratic_denominator_identity n t z hshift hquad
  have hR1 := aperyR_quadratic_denominator_identity (n + 1) (t + 1) z hshift' hquad'
  have hden := aperyQuadraticDenominator_diagonal n t z
  apply mul_left_cancel₀ (aperyQuadraticDenominator_ne_zero n t z hquad)
  calc
    _ = aperyR (n + 1) (t + 1) z *
        (aperyQuadraticDenominator n t z *
          ((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z) *
            ((t + ((n + 2 : ℕ) : ℚ)) ^ 2 + z)) := by ring
    _ = (t ^ 2 + z) *
        (aperyR (n + 1) (t + 1) z * aperyQuadraticDenominator (n + 1) (t + 1) z) := by
          rw [← hden]
          ring
    _ = (t ^ 2 + z) * (t * aperyNumerator n t) ^ 2 := by
          rw [hR1, aperyNumerator_diagonal]
    _ = _ := by rw [mul_pow, ← hR0]; ring

theorem aperyR_diagonal_ratio (n : ℕ) (t z : ℚ)
    (hshift : ∀ j : ℕ, t + (j : ℚ) ≠ 0)
    (hquad : ∀ j : ℕ, (t + (j : ℚ)) ^ 2 + z ≠ 0) :
    aperyR (n + 1) (t + 1) z =
      (t ^ 2 * (t ^ 2 + z) /
        (((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z) *
          ((t + ((n + 2 : ℕ) : ℚ)) ^ 2 + z))) * aperyR n t z := by
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero (hquad (n + 1)) (hquad (n + 2)))).2
  simpa only [mul_assoc] using aperyR_diagonal_cleared n t z hshift hquad

set_option maxHeartbeats 800000 in
theorem aperyR_deformed_telescoping (n : ℕ) (t z : ℚ)
    (hshift : ∀ j : ℕ, t + (j : ℚ) ≠ 0)
    (hquad : ∀ j : ℕ, (t + (j : ℚ)) ^ 2 + z ≠ 0) :
    aperyTelescoperPlus ((n + 1 : ℕ) : ℚ) z * aperyR (n + 2) t z +
      aperyTelescoperMiddle ((n + 1 : ℕ) : ℚ) z * aperyR (n + 1) t z +
      aperyTelescoperMinus ((n + 1 : ℕ) : ℚ) z * aperyR n t z =
    aperyTelescoperCertificate ((n + 1 : ℕ) : ℚ) z (t + 1) *
        aperyR (n + 1) (t + 1) z -
      aperyTelescoperCertificate ((n + 1 : ℕ) : ℚ) z t * aperyR (n + 1) t z := by
  have hden (k : ℕ) : aperyDenominator k t ≠ 0 := by
    unfold aperyDenominator
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hshift j)
  rw [aperyR_succ_ratio (n + 1) t z (hden (n + 1))
    (hshift (n + 2)) (hquad (n + 2))]
  rw [aperyR_succ_ratio n t z (hden n) (hshift (n + 1)) (hquad (n + 1)),
    aperyR_diagonal_ratio n t z hshift hquad]
  have hp := aperyDeformedTelescoper_polynomial_identity (((n + 1 : ℕ) : ℚ)) z t
  have hq1 := hquad (n + 1)
  have hq2 := hquad (n + 2)
  have he : t + (((n + 1 : ℕ) : ℚ)) + 1 = t + (((n + 2 : ℕ) : ℚ)) := by
    push_cast
    ring
  have hm : t - (((n + 1 : ℕ) : ℚ)) - 1 = t - (((n + 2 : ℕ) : ℚ)) := by
    push_cast
    ring
  rw [he, hm] at hp
  generalize ha : (t + (((n + 1 : ℕ) : ℚ))) ^ 2 + z = a at hp hq1 ⊢
  generalize hb : (t + (((n + 2 : ℕ) : ℚ))) ^ 2 + z = b at hp hq2 ⊢
  field_simp [hq1, hq2]
  simp only [show n + 1 + 1 = n + 2 by omega]
  linear_combination (aperyR n t z) * hp

theorem aperyR_deformed_finite_sum (n M : ℕ) (z : ℚ) (hz : 0 ≤ z) :
    (∑ j ∈ Finset.range M,
      (aperyTelescoperPlus ((n + 1 : ℕ) : ℚ) z * aperyR (n + 2) ((j : ℚ) + 1) z +
        aperyTelescoperMiddle ((n + 1 : ℕ) : ℚ) z * aperyR (n + 1) ((j : ℚ) + 1) z +
        aperyTelescoperMinus ((n + 1 : ℕ) : ℚ) z * aperyR n ((j : ℚ) + 1) z)) =
      aperyTelescoperCertificate ((n + 1 : ℕ) : ℚ) z ((M : ℚ) + 1) *
        aperyR (n + 1) ((M : ℚ) + 1) z := by
  induction M with
  | zero =>
      have hzero : aperyR (n + 1) 1 z = 0 := by
        simpa using aperyR_zero_at_integer (n + 1) 0 (by omega) z
      simp [hzero]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := aperyR_deformed_telescoping n ((M : ℚ) + 1) z
        (fun j => ne_of_gt (by positivity : (0 : ℚ) < (M : ℚ) + 1 + (j : ℚ)))
        (fun j => ne_of_gt (add_pos_of_pos_of_nonneg
          (sq_pos_of_pos (by positivity : (0 : ℚ) < (M : ℚ) + 1 + (j : ℚ))) hz))
      push_cast at hstep ⊢
      linarith [hstep]

theorem aperyTelescoperPlus_zero (n : ℚ) :
    aperyTelescoperPlus n 0 = -6 * n ^ 4 * (n + 1) ^ 4 * (n + 1) ^ 3 := by
  unfold aperyTelescoperPlus aperyTelescoperK
  ring

theorem aperyTelescoperMinus_zero (n : ℚ) :
    aperyTelescoperMinus n 0 = -6 * n ^ 4 * (n + 1) ^ 4 * n ^ 3 := by
  unfold aperyTelescoperMinus aperyTelescoperK
  ring

theorem aperyTelescoperMiddle_zero (n : ℚ) :
    aperyTelescoperMiddle n 0 =
      6 * n ^ 4 * (n + 1) ^ 4 * (2 * n + 1) * (17 * n ^ 2 + 17 * n + 5) := by
  unfold aperyTelescoperMiddle
  dsimp
  ring

end OddZeta
