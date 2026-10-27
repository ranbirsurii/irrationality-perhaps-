import Mathlib

/-!
# The first deformed Apéry coefficient

This file formalizes the rational coefficient data stated in the supplied
`r = 2` calculation. In particular, it defines the Apéry coefficients and
the displayed harmonic-number expression for `C n`, and proves the stated
`n = 1` values and scalar elimination identity.

The source text asserts that partial fractions of the infinite series give
these coefficients; that analytic derivation is not part of these finite
rational identities. The Adams projector below is likewise only its scalar
eigenvalue calculation. No regulator class or motivic lift is constructed.
-/

namespace OddZeta

/-- The numerator in the rational Apéry function `F_n(t)`. -/
def aperyNumerator (n : ℕ) (t : ℚ) : ℚ :=
  ∏ j ∈ Finset.range n, (t - (j + 1 : ℚ))

/-- The denominator in the rational Apéry function `F_n(t)`. -/
def aperyDenominator (n : ℕ) (t : ℚ) : ℚ :=
  ∏ j ∈ Finset.range (n + 1), (t + (j : ℚ))

/-- The squared rational function `F_n(t)` used in the supplied deformation. -/
def aperyF (n : ℕ) (t : ℚ) : ℚ :=
  (aperyNumerator n t / aperyDenominator n t) ^ 2

/-- The finite deformation kernel `R_n(t,z)` from the chat text. -/
def aperyR (n : ℕ) (t z : ℚ) : ℚ :=
  aperyF n t * ∏ j ∈ Finset.range (n + 1),
    (1 + z / (t + (j : ℚ)) ^ 2)⁻¹

theorem aperyNumerator_succ (n : ℕ) (t : ℚ) :
    aperyNumerator (n + 1) t =
      aperyNumerator n t * (t - ((n + 1 : ℕ) : ℚ)) := by
  simp [aperyNumerator, Finset.prod_range_succ]

theorem aperyDenominator_succ (n : ℕ) (t : ℚ) :
    aperyDenominator (n + 1) t =
      aperyDenominator n t * (t + ((n + 1 : ℕ) : ℚ)) := by
  simp [aperyDenominator, Finset.prod_range_succ]

/-- The undeformed Apéry rational function has a first-order term ratio. -/
theorem aperyF_succ (n : ℕ) (t : ℚ)
    (hden : aperyDenominator n t ≠ 0)
    (hshift : t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    aperyF (n + 1) t = aperyF n t *
      (((t - ((n + 1 : ℕ) : ℚ)) / (t + ((n + 1 : ℕ) : ℚ))) ^ 2) := by
  unfold aperyF
  rw [aperyNumerator_succ, aperyDenominator_succ]
  field_simp [hden, hshift]

/-- Creative-telescoping recurrence for the actual finite chat kernel.
The old deformation factors cancel structurally; only the new index remains. -/
theorem aperyR_succ (n : ℕ) (t z : ℚ)
    (hden : aperyDenominator n t ≠ 0)
    (hshift : t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    aperyR (n + 1) t z = aperyR n t z *
      (((t - ((n + 1 : ℕ) : ℚ)) / (t + ((n + 1 : ℕ) : ℚ))) ^ 2) *
      (1 + z / (t + ((n + 1 : ℕ) : ℚ)) ^ 2)⁻¹ := by
  unfold aperyR
  rw [aperyF_succ n t hden hshift]
  simp only [Finset.prod_range_succ]
  ring

/-- On the positive real-parameter region, the recurrence is the simple
hypergeometric ratio with quadratic denominator. -/
theorem aperyR_succ_ratio (n : ℕ) (t z : ℚ)
    (hden : aperyDenominator n t ≠ 0)
    (hshift : t + ((n + 1 : ℕ) : ℚ) ≠ 0)
    (hquad : (t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z ≠ 0) :
    aperyR (n + 1) t z = aperyR n t z *
      (((t - ((n + 1 : ℕ) : ℚ)) ^ 2) /
        ((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z)) := by
  rw [aperyR_succ n t z hden hshift]
  field_simp [hshift, hquad]

theorem aperyR_zero_closed_form (t z : ℚ)
    (ht : t ≠ 0) (hquad : t ^ 2 + z ≠ 0) :
    aperyR 0 t z = (t ^ 2 + z)⁻¹ := by
  norm_num [aperyR, aperyF, aperyNumerator, aperyDenominator]
  field_simp [ht, hquad]

theorem quadratic_kernel_factor_cancel (a b z : ℚ)
    (hb : b ≠ 0) (hquad : b ^ 2 + z ≠ 0) :
    (b ^ 2 + z) * (a / b) ^ 2 * (1 + z / b ^ 2)⁻¹ = a ^ 2 := by
  field_simp [hb, hquad]

noncomputable def eulerPowerSeries (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.X * PowerSeries.derivative ℚ f

noncomputable def eulerShiftPowerSeries (c : ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  eulerPowerSeries f + PowerSeries.C c * f

theorem coeff_eulerPowerSeries (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (eulerPowerSeries f) =
      (n : ℚ) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp [eulerPowerSeries]
  | succ n =>
      simp [eulerPowerSeries, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_derivative]
      ring

theorem coeff_eulerShiftPowerSeries (c : ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (eulerShiftPowerSeries c f) =
      ((n : ℚ) + c) * PowerSeries.coeff n f := by
  simp [eulerShiftPowerSeries, coeff_eulerPowerSeries,
    PowerSeries.coeff_C_mul]
  ring

theorem coeff_eulerShiftPowerSeries_sq (c : ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (eulerShiftPowerSeries c (eulerShiftPowerSeries c f)) =
      ((n : ℚ) + c) ^ 2 * PowerSeries.coeff n f := by
  rw [coeff_eulerShiftPowerSeries, coeff_eulerShiftPowerSeries]
  ring

theorem eulerShiftPowerSeries_sq_expansion (c : ℚ) (f : PowerSeries ℚ) :
    eulerShiftPowerSeries c (eulerShiftPowerSeries c f) =
      eulerPowerSeries (eulerPowerSeries f) +
        PowerSeries.C (2 * c) * eulerPowerSeries f +
        PowerSeries.C (c ^ 2) * f := by
  apply PowerSeries.ext
  intro n
  rw [coeff_eulerShiftPowerSeries_sq, map_add, map_add,
    coeff_eulerPowerSeries, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul]
  rw [coeff_eulerPowerSeries]
  ring

noncomputable def aperyKernelEulerOperator (t z : ℚ)
    (f : PowerSeries ℚ) : PowerSeries ℚ :=
  eulerShiftPowerSeries t (eulerShiftPowerSeries t f) +
    PowerSeries.C z * f

theorem eulerShiftPowerSeries_sub (c : ℚ) (f g : PowerSeries ℚ) :
    eulerShiftPowerSeries c (f - g) =
      eulerShiftPowerSeries c f - eulerShiftPowerSeries c g := by
  simp [eulerShiftPowerSeries, eulerPowerSeries, map_sub]
  ring

theorem aperyKernelEulerOperator_sub_const (t z : ℚ)
    (f : PowerSeries ℚ) (c : ℚ) :
    aperyKernelEulerOperator t z (f - PowerSeries.C c) =
      aperyKernelEulerOperator t z f -
        PowerSeries.C ((t ^ 2 + z) * c) := by
  rw [aperyKernelEulerOperator, eulerShiftPowerSeries_sub,
    eulerShiftPowerSeries_sub, aperyKernelEulerOperator]
  simp [eulerShiftPowerSeries, eulerPowerSeries]
  ring

noncomputable def sequencePowerSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk a

@[simp] theorem coeff_sequencePowerSeries (a : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (sequencePowerSeries a) = a n := by
  simp [sequencePowerSeries]

@[simp] theorem coeff_sequencePowerSeries_sub_const_succ
    (a : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (sequencePowerSeries a - PowerSeries.C (a 0)) = a (n + 1) := by
  simp [sequencePowerSeries]

/-- A first-order coefficient recurrence is exactly the second-order
formal differential equation for its generating series. This is the
coefficientwise creative-telescoping step. -/
theorem recurrence_implies_generating_series_equation
    (a : ℕ → ℚ) (t z : ℚ)
    (hrec : ∀ n,
      (((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z) * a (n + 1) =
        (t - ((n + 1 : ℕ) : ℚ)) ^ 2 * a n)) :
    eulerShiftPowerSeries t
        (eulerShiftPowerSeries t
          (sequencePowerSeries a - PowerSeries.C (a 0))) +
      PowerSeries.C z * (sequencePowerSeries a - PowerSeries.C (a 0)) =
    PowerSeries.X *
      eulerShiftPowerSeries (1 - t)
        (eulerShiftPowerSeries (1 - t) (sequencePowerSeries a)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      have hz : PowerSeries.coeff 0
          (sequencePowerSeries a - PowerSeries.C (a 0)) = 0 := by
        simp [sequencePowerSeries]
      rw [map_add, coeff_eulerShiftPowerSeries_sq,
        PowerSeries.coeff_C_mul, hz]
      simp
  | succ n =>
      have hL : PowerSeries.coeff (n + 1)
          (eulerShiftPowerSeries t
            (eulerShiftPowerSeries t
              (sequencePowerSeries a - PowerSeries.C (a 0))) +
            PowerSeries.C z * (sequencePowerSeries a -
              PowerSeries.C (a 0))) =
          (((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z) * a (n + 1)) := by
        rw [map_add, coeff_eulerShiftPowerSeries_sq,
          PowerSeries.coeff_C_mul, coeff_sequencePowerSeries_sub_const_succ]
        push_cast
        ring
      have hR : PowerSeries.coeff (n + 1)
          (PowerSeries.X *
            eulerShiftPowerSeries (1 - t)
              (eulerShiftPowerSeries (1 - t) (sequencePowerSeries a))) =
          ((t - ((n + 1 : ℕ) : ℚ)) ^ 2 * a n) := by
        rw [PowerSeries.coeff_succ_X_mul, coeff_eulerShiftPowerSeries_sq,
          coeff_sequencePowerSeries]
        push_cast
        ring
      rw [hL, hR]
      exact hrec n

/-- The generating series of the deformed Apéry kernels obeys the exact
second-order Euler-operator equation obtained from their certified ratio. -/
theorem aperyR_generating_series_equation (t z : ℚ)
    (hden : ∀ n, aperyDenominator n t ≠ 0)
    (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0)
    (hquad : ∀ n, (t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z ≠ 0) :
    eulerShiftPowerSeries t
        (eulerShiftPowerSeries t
          (sequencePowerSeries (fun n => aperyR n t z) -
            PowerSeries.C (aperyR 0 t z))) +
      PowerSeries.C z *
        (sequencePowerSeries (fun n => aperyR n t z) -
          PowerSeries.C (aperyR 0 t z)) =
    PowerSeries.X *
      eulerShiftPowerSeries (1 - t)
        (eulerShiftPowerSeries (1 - t)
          (sequencePowerSeries (fun n => aperyR n t z))) := by
  apply recurrence_implies_generating_series_equation
  intro n
  rw [aperyR_succ n t z (hden n) (hshift n)]
  let b := t + ((n + 1 : ℕ) : ℚ)
  have hb : b ≠ 0 := by simpa [b] using hshift n
  have hquad' : b ^ 2 + z ≠ 0 := by simpa [b] using hquad n
  calc
    (b ^ 2 + z) *
        (aperyR n t z *
          (((t - ((n + 1 : ℕ) : ℚ)) / b) ^ 2) *
            (1 + z / b ^ 2)⁻¹) =
        (t - ((n + 1 : ℕ) : ℚ)) ^ 2 * aperyR n t z := by
      rw [show (t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z = b ^ 2 + z by rfl]
      calc
        (b ^ 2 + z) *
            (aperyR n t z *
              (((t - ((n + 1 : ℕ) : ℚ)) / b) ^ 2) *
                (1 + z / b ^ 2)⁻¹) =
            aperyR n t z *
              ((b ^ 2 + z) *
                (((t - ((n + 1 : ℕ) : ℚ)) / b) ^ 2) *
                  (1 + z / b ^ 2)⁻¹) := by ring
        _ = aperyR n t z * (t - ((n + 1 : ℕ) : ℚ)) ^ 2 := by
          rw [quadratic_kernel_factor_cancel _ b z hb hquad']
        _ = (t - ((n + 1 : ℕ) : ℚ)) ^ 2 * aperyR n t z := by ring

/-- The same recurrence, expanded at the initial coefficient, is the
inhomogeneous Euler equation with unit forcing. -/
theorem aperyR_generating_series_inhomogeneous (t z : ℚ)
    (ht : t ≠ 0) (hzero : t ^ 2 + z ≠ 0)
    (hden : ∀ n, aperyDenominator n t ≠ 0)
    (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0)
    (hquad : ∀ n, (t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z ≠ 0) :
    aperyKernelEulerOperator t z
        (sequencePowerSeries (fun n => aperyR n t z)) =
      PowerSeries.X *
          eulerShiftPowerSeries (1 - t)
            (eulerShiftPowerSeries (1 - t)
              (sequencePowerSeries (fun n => aperyR n t z))) +
        PowerSeries.C 1 := by
  let G := sequencePowerSeries (fun n => aperyR n t z)
  let c := aperyR 0 t z
  have hcenter : aperyKernelEulerOperator t z (G - PowerSeries.C c) =
      PowerSeries.X * eulerShiftPowerSeries (1 - t)
        (eulerShiftPowerSeries (1 - t) G) := by
    simpa [G, aperyKernelEulerOperator] using
      aperyR_generating_series_equation t z hden hshift hquad
  have hforce : (t ^ 2 + z) * c = 1 := by
    dsimp [c]
    rw [aperyR_zero_closed_form t z ht hzero]
    field_simp [hzero]
  calc
    aperyKernelEulerOperator t z G =
        aperyKernelEulerOperator t z (G - PowerSeries.C c) +
          PowerSeries.C ((t ^ 2 + z) * c) := by
      rw [aperyKernelEulerOperator_sub_const]
      abel
    _ = PowerSeries.X * eulerShiftPowerSeries (1 - t)
          (eulerShiftPowerSeries (1 - t) G) + PowerSeries.C 1 := by
      rw [hcenter, hforce]

theorem aperyDenominator_pos (n : ℕ) (t : ℚ) (ht : 0 < t) :
    0 < aperyDenominator n t := by
  unfold aperyDenominator
  apply Finset.prod_pos
  intro j hj
  positivity

/-- A concrete nonsingular parameter region for the formal generating-series
equation: positive `t` and nonnegative `z` discharge every denominator side
condition used by the term recurrence. -/
theorem aperyR_generating_series_inhomogeneous_on_positive_region
    (t z : ℚ) (ht : 0 < t) (hz : 0 ≤ z) :
    aperyKernelEulerOperator t z
        (sequencePowerSeries (fun n => aperyR n t z)) =
      PowerSeries.X *
          eulerShiftPowerSeries (1 - t)
            (eulerShiftPowerSeries (1 - t)
              (sequencePowerSeries (fun n => aperyR n t z))) +
        PowerSeries.C 1 := by
  apply aperyR_generating_series_inhomogeneous
  · exact ne_of_gt ht
  · positivity
  · intro n
    exact ne_of_gt (aperyDenominator_pos n t ht)
  · intro n
    positivity
  · intro n
    apply ne_of_gt
    have hn : 0 < t + ((n + 1 : ℕ) : ℚ) := by positivity
    have hsquare : 0 < (t + ((n + 1 : ℕ) : ℚ)) ^ 2 := sq_pos_of_pos hn
    exact add_pos_of_pos_of_nonneg hsquare hz

/-- Each integer zero of the numerator remains a zero of the deformed kernel. -/
theorem aperyR_zero_at_integer (n i : ℕ) (hi : i < n) (z : ℚ) :
    aperyR n (i + 1 : ℚ) z = 0 := by
  have hnum : aperyNumerator n (i + 1 : ℚ) = 0 := by
    unfold aperyNumerator
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    simp
  simp [aperyR, aperyF, hnum]

/-- The rational harmonic number `H_n`. -/
def harmonic (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (j + 1 : ℚ)⁻¹

/-- The rational second-order harmonic number `H_n^(2)`. -/
def harmonicTwo (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (j + 1 : ℚ)⁻¹ ^ 2

def harmonicThree (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (j + 1 : ℚ)⁻¹ ^ 3

def harmonicFour (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (j + 1 : ℚ)⁻¹ ^ 4

def harmonicFive (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (j + 1 : ℚ)⁻¹ ^ 5

/-- The rational Apéry summand `binom(n,k)^2 binom(n+k,k)^2`. -/
def aperySummand (n k : ℕ) : ℚ :=
  ((Nat.choose n k : ℚ) ^ 2) * ((Nat.choose (n + k) k : ℚ) ^ 2)

def aperySummandNat (n k : ℕ) : ℕ :=
  (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2

/-- The Apéry denominator coefficient `A_n`. -/
def aperyA (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), aperySummand n k

def aperyANat (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), aperySummandNat n k

theorem aperyA_eq_natCast (n : ℕ) : aperyA n = (aperyANat n : ℚ) := by
  simp [aperyA, aperyANat, aperySummand, aperySummandNat]

/-- The harmonic combination `eta_(n,k)` from the source calculation. -/
def aperyEta (n k : ℕ) : ℚ :=
  harmonic (n + k) + harmonic (n - k) - 2 * harmonic k

/-- Local logarithmic coefficients of `F_n` at the pole `t = -k`. -/
def aperyLocalSecond (n k : ℕ) : ℚ :=
  harmonicTwo (n + k) - 2 * harmonicTwo k - harmonicTwo (n - k)

def aperyLocalThird (n k : ℕ) : ℚ :=
  -harmonicThree (n + k) + 2 * harmonicThree k - harmonicThree (n - k)

def aperyLocalRegular0 (n k : ℕ) : ℚ :=
  2 * aperyEta n k ^ 2 - aperyLocalSecond n k

def aperyLocalRegular1 (n k : ℕ) : ℚ :=
  -(4 : ℚ) / 3 * aperyEta n k ^ 3 +
    2 * aperyEta n k * aperyLocalSecond n k +
    (2 : ℚ) / 3 * aperyLocalThird n k

def aperyPoleRegular0 (n k : ℕ) : ℚ :=
  harmonicTwo k + harmonicTwo (n - k)

def aperyPoleRegular1 (n k : ℕ) : ℚ :=
  2 * harmonicThree k - 2 * harmonicThree (n - k)

/-- The explicitly stated coefficient of `zeta(3)` in `L_(n,1)`. -/
def aperyC (n : ℕ) : ℚ :=
  -2 * ∑ k ∈ Finset.range (n + 1),
    aperySummand n k *
      (2 * aperyEta n k ^ 2 - harmonicTwo (n + k) +
        3 * harmonicTwo k + 2 * harmonicTwo (n - k))

/-- Laurent coefficients of the first deformation coefficient of `R_n` at
`t = -k`, ordered from the fourth-order pole down to the simple pole. -/
def aperyR1Pole4 (n k : ℕ) : ℚ :=
  -aperySummand n k

def aperyR1Pole3 (n k : ℕ) : ℚ :=
  2 * aperySummand n k * aperyEta n k

def aperyR1Pole2 (n k : ℕ) : ℚ :=
  -aperySummand n k * (aperyLocalRegular0 n k + aperyPoleRegular0 n k)

def aperyR1Pole1 (n k : ℕ) : ℚ :=
  -aperySummand n k *
    (aperyLocalRegular1 n k -
      2 * aperyEta n k * aperyPoleRegular0 n k + aperyPoleRegular1 n k)

/-- Rational part of the ordinary Apéry form from the pole expansion. -/
def aperyB (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    aperySummand n k *
      (2 * harmonicThree k - 2 * aperyEta n k * harmonicTwo k)

/-- Rational part of the first deformation form from its Laurent coefficients. -/
def aperyE (n : ℕ) : ℚ :=
  -∑ k ∈ Finset.range (n + 1),
    (4 * aperyR1Pole4 n k * harmonicFive k +
      3 * aperyR1Pole3 n k * harmonicFour k +
      2 * aperyR1Pole2 n k * harmonicThree k +
      aperyR1Pole1 n k * harmonicTwo k)

def aperyProjectedA (n : ℕ) : ℤ :=
  -4 * (aperyANat n : ℤ)

theorem aperyProjectedA_eq_rationalCoefficient (n : ℕ) :
    (aperyProjectedA n : ℚ) = -4 * aperyA n := by
  rw [aperyA_eq_natCast]
  norm_num [aperyProjectedA]

def aperyProjectedB (n : ℕ) : ℚ :=
  (7 : ℚ) / 24 * aperyE n

/-- The exact reduced denominator of the projected rational term. -/
def aperyProjectedDenom (n : ℕ) : ℕ :=
  (aperyProjectedB n).den

def aperyProjectedForm (n : ℕ) (zeta5 : ℝ) : ℝ :=
  (aperyProjectedA n : ℝ) * zeta5 - (aperyProjectedB n : ℝ)

theorem aperyProjectedDenom_clears (n : ℕ) :
    (aperyProjectedDenom n : ℚ) * aperyProjectedB n =
      (aperyProjectedB n).num := by
  have hq := (aperyProjectedB n).num_div_den
  have hd : ((aperyProjectedB n).den : ℚ) ≠ 0 := by
    exact_mod_cast Rat.den_nz (aperyProjectedB n)
  have hmul : ((aperyProjectedB n).den : ℚ) * aperyProjectedB n =
      (aperyProjectedB n).num := by
    calc
      ((aperyProjectedB n).den : ℚ) * aperyProjectedB n =
          ((aperyProjectedB n).den : ℚ) *
            (((aperyProjectedB n).num : ℚ) / (aperyProjectedB n).den) :=
        congrArg (fun x : ℚ => ((aperyProjectedB n).den : ℚ) * x) hq.symm
      _ = (aperyProjectedB n).num := by field_simp [hd]
  exact hmul

/-- The zeta-five form after the proposed weight projector, in rational
coefficient form. -/
theorem aperyC_eq_twice_pole2_sum (n : ℕ) :
    aperyC n = 2 * ∑ k ∈ Finset.range (n + 1), aperyR1Pole2 n k := by
  unfold aperyC
  have hsum :
      (∑ k ∈ Finset.range (n + 1), aperyR1Pole2 n k) =
        -(∑ k ∈ Finset.range (n + 1),
          aperySummand n k *
            (2 * aperyEta n k ^ 2 - harmonicTwo (n + k) +
              3 * harmonicTwo k + 2 * harmonicTwo (n - k))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    unfold aperyR1Pole2 aperySummand aperyLocalRegular0
      aperyLocalSecond aperyPoleRegular0
    ring
  rw [hsum]
  ring

theorem aperyA_one : aperyA 1 = 5 := by
  norm_num [aperyA, aperySummand, Finset.sum_range_succ]

theorem aperyC_one : aperyC 1 = -36 := by
  norm_num [aperyC, aperySummand, aperyEta, harmonic, harmonicTwo,
    Finset.sum_range_succ]

theorem aperyB_one : aperyB 1 = 12 := by
  norm_num [aperyB, aperySummand, aperyEta, harmonic, harmonicTwo,
    harmonicThree, Finset.sum_range_succ]

theorem aperyE_one : aperyE 1 = 64 := by
  norm_num [aperyE, aperySummand, aperyR1Pole4, aperyR1Pole3,
    aperyR1Pole2, aperyR1Pole1, aperyEta, aperyLocalRegular0,
    aperyLocalRegular1, aperyLocalSecond, aperyLocalThird,
    aperyPoleRegular0, aperyPoleRegular1, harmonic, harmonicTwo,
    harmonicThree, harmonicFour, harmonicFive, Finset.sum_range_succ]

/-- The two stated coefficient formulas, with their rational terms exposed. -/
def aperyL0 (n : ℕ) (zeta3 : ℝ) : ℝ :=
  2 * (aperyA n : ℝ) * zeta3 - (aperyB n : ℝ)

def aperyL1 (n : ℕ) (zeta3 zeta5 : ℝ) : ℝ :=
  -4 * (aperyA n : ℝ) * zeta5 + (aperyC n : ℝ) * zeta3 + (aperyE n : ℝ)

/-- Scalar elimination cancels the `zeta(3)` term exactly. -/
theorem apery_scalar_elimination
    (n : ℕ) (zeta3 zeta5 : ℝ) :
    2 * (aperyA n : ℝ) * aperyL1 n zeta3 zeta5 -
        (aperyC n : ℝ) * aperyL0 n zeta3 =
      -8 * (aperyA n : ℝ) ^ 2 * zeta5 +
        ((2 * aperyA n * aperyE n + aperyC n * aperyB n : ℚ) : ℝ) := by
  unfold aperyL0 aperyL1
  push_cast
  ring

/-- The `n = 1` first-level forms recorded in the source. -/
theorem apery_L0_one (zeta3 : ℝ) :
    aperyL0 1 zeta3 = 10 * zeta3 - 12 := by
  unfold aperyL0
  rw [aperyA_one, aperyB_one]
  norm_num

theorem apery_L1_one (zeta3 zeta5 : ℝ) :
    aperyL1 1 zeta3 zeta5 = -20 * zeta5 - 36 * zeta3 + 64 := by
  unfold aperyL1
  rw [aperyA_one, aperyC_one, aperyE_one]
  norm_num
  ring

/-- The displayed `n = 1` scalar elimination check. -/
theorem apery_elimination_one (zeta3 zeta5 : ℝ) :
    10 * (-20 * zeta5 - 36 * zeta3 + 64) +
        36 * (10 * zeta3 - 12) = -200 * zeta5 + 208 := by
  ring

/-- The scalar polynomial corresponding to `(psi_2 - 8 I) / 24`. -/
def adamsProjector5Eigenvalue (eigenvalue : ℚ) : ℚ :=
  (eigenvalue - 8) / 24

/-- Apply `(psi_2 - 8 I) / 24` to a vector in a rational vector space. -/
def adamsProjector5Apply {V : Type} [AddCommGroup V] [Module ℚ V]
    (psi : V →ₗ[ℚ] V) (v : V) : V :=
  (1 / 24 : ℚ) • (psi v - (8 : ℚ) • v)

theorem adamsProjector5Apply_kills_weight3 {V : Type}
    [AddCommGroup V] [Module ℚ V] (psi : V →ₗ[ℚ] V) (v : V)
    (hpsi : psi v = (8 : ℚ) • v) :
    adamsProjector5Apply psi v = 0 := by
  simp [adamsProjector5Apply, hpsi]

theorem adamsProjector5Apply_fixes_weight5 {V : Type}
    [AddCommGroup V] [Module ℚ V] (psi : V →ₗ[ℚ] V) (v : V)
    (hpsi : psi v = (32 : ℚ) • v) :
    adamsProjector5Apply psi v = v := by
  unfold adamsProjector5Apply
  rw [hpsi]
  have h : (32 : ℚ) • v - (8 : ℚ) • v = (24 : ℚ) • v := by
    module
  rw [h]
  simp [smul_smul]

/-- The proposed Adams action on the three specified weights `3`, `5`, and
`0`, with eigenvalues `8`, `32`, and `1`. -/
def adamsTwoOnWeights : (ℚ × ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ × ℚ) where
  toFun v := (8 * v.1, 32 * v.2.1, v.2.2)
  map_add' v w := by
    ext <;> simp <;> ring
  map_smul' c v := by
    ext <;> simp <;> ring

theorem adamsProjector5_weight_coordinates (v : ℚ × ℚ × ℚ) :
    adamsProjector5Apply adamsTwoOnWeights v =
      (0, v.2.1, -(7 : ℚ) / 24 * v.2.2) := by
  ext <;> simp [adamsProjector5Apply, adamsTwoOnWeights] <;> ring

/-- Period evaluation of the formal weight coordinates. -/
def weightPeriod (zeta3 zeta5 : ℝ) (v : ℚ × ℚ × ℚ) : ℝ :=
  (v.1 : ℝ) * zeta3 + (v.2.1 : ℝ) * zeta5 + (v.2.2 : ℝ)

/-- The projector removes the `zeta(3)` coordinate at fixed denominator 24. -/
theorem adamsProjector5_weightPeriod (zeta3 zeta5 : ℝ)
    (v : ℚ × ℚ × ℚ) :
    weightPeriod zeta3 zeta5 (adamsProjector5Apply adamsTwoOnWeights v) =
      (v.2.1 : ℝ) * zeta5 - (7 : ℝ) / 24 * (v.2.2 : ℝ) := by
  rw [adamsProjector5_weight_coordinates]
  unfold weightPeriod
  push_cast
  ring

/-- The formal weight decomposition of the first deformed Apéry coefficient.
This records the proposed grading; it is not a construction of a geometric
regulator class. -/
def aperyL1WeightCoordinates (n : ℕ) : ℚ × ℚ × ℚ :=
  (aperyC n, -4 * aperyA n, aperyE n)

theorem aperyL1_projected_period (n : ℕ) (zeta3 zeta5 : ℝ) :
    weightPeriod zeta3 zeta5
      (adamsProjector5Apply adamsTwoOnWeights (aperyL1WeightCoordinates n)) =
        -4 * (aperyA n : ℝ) * zeta5 -
          (7 : ℝ) / 24 * (aperyE n : ℝ) := by
  rw [adamsProjector5_weight_coordinates]
  unfold weightPeriod aperyL1WeightCoordinates
  push_cast
  ring

theorem aperyL1_projected_period_eq_form (n : ℕ) (zeta3 zeta5 : ℝ) :
    weightPeriod zeta3 zeta5
      (adamsProjector5Apply adamsTwoOnWeights (aperyL1WeightCoordinates n)) =
        aperyProjectedForm n zeta5 := by
  rw [aperyL1_projected_period]
  unfold aperyProjectedForm aperyProjectedB
  have hA : (aperyProjectedA n : ℝ) = -4 * (aperyA n : ℝ) := by
    exact_mod_cast aperyProjectedA_eq_rationalCoefficient n
  rw [← hA]
  push_cast
  ring

theorem adamsProjector5_kills_weight3 :
    adamsProjector5Eigenvalue 8 = 0 := by
  norm_num [adamsProjector5Eigenvalue]

theorem adamsProjector5_fixes_weight5 :
    adamsProjector5Eigenvalue 32 = 1 := by
  norm_num [adamsProjector5Eigenvalue]

theorem adamsProjector5_scales_weight0_rational_part :
    adamsProjector5Eigenvalue 1 = -(7 : ℚ) / 24 := by
  norm_num [adamsProjector5Eigenvalue]

end OddZeta
