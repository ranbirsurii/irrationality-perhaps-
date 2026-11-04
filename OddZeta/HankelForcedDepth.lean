import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OddZeta

theorem prime_power_denominator_of_negative_valuation
    (p a : ℕ) (hp : p.Prime) (x : ℚ)
    (hv : padicValRat p x = -(a : ℤ)) : p ^ a ∣ x.den := by
  have hn : (0 : ℤ) ≤ padicValInt p x.num := by
    exact Int.natCast_nonneg _
  have hd : a ≤ padicValNat p x.den := by
    rw [padicValRat_def] at hv
    omega
  exact (Nat.pow_dvd_iff_le_padicValNat hp.ne_one x.den_ne_zero).mpr hd

theorem scaled_unit_coefficient_forces_prime_power_denominator
    (p a i : ℕ) [hp : Fact p.Prime] (P : Polynomial ℚ)
    (hn : (P.scaleRoots ((p : ℚ) ^ a)).coeff i ≠ 0)
    (hu : padicValRat p ((P.scaleRoots ((p : ℚ) ^ a)).coeff i) = 0) :
    p ^ (a * (P.natDegree - i)) ∣ (P.coeff i).den := by
  have hpn : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hc : P.coeff i ≠ 0 := by
    intro h
    apply hn
    simp [Polynomial.coeff_scaleRoots, h]
  have hv : padicValRat p (P.coeff i) =
      -((a * (P.natDegree - i) : ℕ) : ℤ) := by
    rw [Polynomial.coeff_scaleRoots,
      padicValRat.mul hc (pow_ne_zero _ (pow_ne_zero a hpn)),
      padicValRat.pow, padicValRat.pow,
      padicValRat.self hp.out.one_lt] at hu
    push_cast
    nlinarith
  exact prime_power_denominator_of_negative_valuation p _ hp.out _ hv

theorem terminal_pole_model_coefficient
    {F : Type*} [Field F] (a b : ℕ) :
    ((Polynomial.X : Polynomial F) ^ a *
      ((Polynomial.X - Polynomial.C (1 / 2 : F)) *
        (Polynomial.X - 1) ^ b)).coeff a = (-1 : F) ^ (b + 1) / 2 := by
  calc
    _ = ((Polynomial.X - Polynomial.C (1 / 2 : F)) *
        (Polynomial.X - 1) ^ b).coeff 0 := by
      simpa only [Nat.zero_add] using Polynomial.coeff_X_pow_mul
        ((Polynomial.X - Polynomial.C (1 / 2 : F)) *
          (Polynomial.X - 1) ^ b) a 0
    _ = _ := by
      have hb : ((Polynomial.X - 1 : Polynomial F) ^ b).coeff 0 =
          (-1 : F) ^ b := by
        induction b with
        | zero => simp
        | succ b ih =>
          rw [pow_succ, Polynomial.mul_coeff_zero, ih]
          simp [pow_succ]
      rw [Polynomial.mul_coeff_zero, hb]
      simp [pow_succ]
      ring

theorem scaled_pole_boundary_value (p c : ℚ) (k : ℕ)
    (hp : p ≠ 0) (hc : c ≠ 0) :
    p ^ (k + 1) * ((1 / (2 * p) - 1 / c) / p ^ k -
      1 / p ^ (k + 1)) = -1 / 2 - p / c := by
  rw [pow_succ]
  field_simp
  ring

end OddZeta
