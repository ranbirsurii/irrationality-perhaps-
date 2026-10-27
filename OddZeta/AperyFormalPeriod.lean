import OddZeta.AperyModernIdentification
import Mathlib.RingTheory.PowerSeries.Derivative

namespace OddZeta

noncomputable def modernEuler {R : Type*} [CommRing R]
    (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.X * PowerSeries.derivative R f

theorem coeff_modernEuler {R : Type*} [CommRing R]
    (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (modernEuler f) = (n : R) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp [modernEuler]
  | succ n =>
    simp [modernEuler, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    ring

noncomputable def modernAperyPF {R : Type*} [CommRing R]
    (f : PowerSeries R) : PowerSeries R :=
  modernEuler (modernEuler (modernEuler f)) -
    PowerSeries.X *
      (PowerSeries.C 34 * modernEuler (modernEuler (modernEuler f)) +
        PowerSeries.C 51 * modernEuler (modernEuler f) +
        PowerSeries.C 27 * modernEuler f + PowerSeries.C 5 * f) +
    PowerSeries.X * (PowerSeries.X *
      (modernEuler (modernEuler (modernEuler f)) +
        PowerSeries.C 3 * modernEuler (modernEuler f) +
        PowerSeries.C 3 * modernEuler f + f))

theorem modernAperyPF_coeff_one {R : Type*} [CommRing R] (f : PowerSeries R) :
    PowerSeries.coeff 1 (modernAperyPF f) =
      PowerSeries.coeff 1 f - 5 * PowerSeries.coeff 0 f := by
  simp only [modernAperyPF, map_add, map_sub, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_C_mul, coeff_modernEuler, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul]
  simp

theorem modernAperyPF_coeff_succ_succ {R : Type*} [CommRing R]
    (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (n + 2) (modernAperyPF f) =
      ((n : R) + 2) ^ 3 * PowerSeries.coeff (n + 2) f -
        (2 * (n : R) + 3) *
          (17 * ((n : R) + 1) ^ 2 + 17 * ((n : R) + 1) + 5) *
            PowerSeries.coeff (n + 1) f +
        ((n : R) + 1) ^ 3 * PowerSeries.coeff n f := by
  simp only [modernAperyPF, map_add, map_sub, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_C_mul, coeff_modernEuler, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem modernAperyPF_first_coefficient {R : Type*} [CommRing R]
    (f : PowerSeries R) (c : R)
    (hf : modernAperyPF f = PowerSeries.C c * PowerSeries.X) :
    PowerSeries.coeff 1 f = 5 * PowerSeries.coeff 0 f + c := by
  have h := congrArg (PowerSeries.coeff 1) hf
  rw [modernAperyPF_coeff_one] at h
  norm_num only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X] at h
  simp only [ite_true, mul_one] at h
  linear_combination h

theorem modernAperyPF_recurrence {R : Type*} [Field R] [CharZero R]
    (f : PowerSeries R) (c : R)
    (hf : modernAperyPF f = PowerSeries.C c * PowerSeries.X) (n : ℕ) :
    PowerSeries.coeff (n + 2) f =
      modernAperyStep n (PowerSeries.coeff n f) (PowerSeries.coeff (n + 1) f) := by
  have h := congrArg (PowerSeries.coeff (n + 2)) hf
  rw [modernAperyPF_coeff_succ_succ] at h
  have hindex : n + 2 ≠ 1 := by omega
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
    ite_eq_right hindex, mul_zero] at h
  have hden : ((n : R) + 2) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (show n + 2 ≠ 0 by omega)
  unfold modernAperyStep
  apply (eq_div_iff hden).mpr
  linear_combination h

theorem aperyV12_identification_from_PF {R : Type*} [Field R] [CharZero R]
    (a b v : PowerSeries R) (z : R)
    (ha : modernAperyPF a = 0)
    (hb : modernAperyPF b = PowerSeries.C 12 * PowerSeries.X)
    (hv : modernAperyPF v = PowerSeries.C (-12) * PowerSeries.X)
    (ha0 : PowerSeries.coeff 0 a = 1)
    (hb0 : PowerSeries.coeff 0 b = 0)
    (hv0 : PowerSeries.coeff 0 v = 2 * z) :
    v = PowerSeries.C (2 * z) * a - b := by
  have ha' : modernAperyPF a = PowerSeries.C 0 * PowerSeries.X := by simpa using ha
  have ha1 := modernAperyPF_first_coefficient a 0 ha'
  have hb1 := modernAperyPF_first_coefficient b 12 hb
  have hv1 := modernAperyPF_first_coefficient v (-12) hv
  have h := aperyV12_period_identification_of_recurrences
    (fun n => PowerSeries.coeff n a) (fun n => PowerSeries.coeff n b)
    (fun n => PowerSeries.coeff n v) z ha0 (by simpa [ha0] using ha1)
    hb0 (by simpa [hb0] using hb1) hv0
    (by rw [hv0] at hv1; convert hv1 using 1; ring)
    (modernAperyPF_recurrence a 0 ha')
    (modernAperyPF_recurrence b 12 hb) (modernAperyPF_recurrence v (-12) hv)
  apply PowerSeries.ext
  intro n
  rw [map_sub, PowerSeries.coeff_C_mul, h n]
  ring

end OddZeta
