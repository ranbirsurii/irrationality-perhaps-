import OddZeta.AperyFive

namespace OddZeta

noncomputable def quadraticInverseSeries (a : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun m => (-1 / a ^ 2) ^ m / a ^ 2)

theorem coeff_quadraticInverseSeries (a : ℚ) (m : ℕ) :
    PowerSeries.coeff m (quadraticInverseSeries a) =
      (-1 / a ^ 2) ^ m / a ^ 2 := by
  simp [quadraticInverseSeries]

theorem quadraticInverseSeries_coefficient_step (a : ℚ) (ha : a ≠ 0)
    (m : ℕ) :
    a ^ 2 * PowerSeries.coeff (m + 1) (quadraticInverseSeries a) +
      PowerSeries.coeff m (quadraticInverseSeries a) = 0 := by
  simp only [coeff_quadraticInverseSeries]
  rw [pow_succ (-1 / a ^ 2) m]
  generalize (-1 / a ^ 2) ^ m = u
  field_simp [ha]
  ring

theorem quadraticInverseSeries_cancel (a : ℚ) (ha : a ≠ 0) :
    (PowerSeries.C (a ^ 2) + PowerSeries.X) * quadraticInverseSeries a = 1 := by
  apply PowerSeries.ext
  intro m
  rw [add_mul, map_add, PowerSeries.coeff_C_mul]
  cases m with
  | zero =>
      simp [coeff_quadraticInverseSeries]
      field_simp [ha]
  | succ m =>
      rw [PowerSeries.coeff_succ_X_mul]
      simpa using quadraticInverseSeries_coefficient_step a ha m

noncomputable def aperyDeformationSeries : ℕ → ℚ → PowerSeries ℚ
  | 0, t => quadraticInverseSeries t
  | n + 1, t =>
      PowerSeries.C ((t - ((n + 1 : ℕ) : ℚ)) ^ 2) *
        aperyDeformationSeries n t *
          quadraticInverseSeries (t + ((n + 1 : ℕ) : ℚ))

noncomputable def aperyDeformationCoefficient (n m : ℕ) (t : ℚ) : ℚ :=
  PowerSeries.coeff m (aperyDeformationSeries n t)

theorem aperyDeformationSeries_step (n : ℕ) (t : ℚ)
    (hshift : t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    (PowerSeries.C ((t + ((n + 1 : ℕ) : ℚ)) ^ 2) + PowerSeries.X) *
        aperyDeformationSeries (n + 1) t =
      PowerSeries.C ((t - ((n + 1 : ℕ) : ℚ)) ^ 2) *
        aperyDeformationSeries n t := by
  dsimp only [aperyDeformationSeries]
  calc
    _ = (PowerSeries.C ((t - ((n + 1 : ℕ) : ℚ)) ^ 2) *
        aperyDeformationSeries n t) *
        ((PowerSeries.C ((t + ((n + 1 : ℕ) : ℚ)) ^ 2) + PowerSeries.X) *
          quadraticInverseSeries (t + ((n + 1 : ℕ) : ℚ))) := by ring
    _ = _ := by rw [quadraticInverseSeries_cancel _ hshift]; simp

theorem aperyDeformationCoefficient_step_zero (n : ℕ) (t : ℚ)
    (hshift : t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    (t + ((n + 1 : ℕ) : ℚ)) ^ 2 * aperyDeformationCoefficient (n + 1) 0 t =
      (t - ((n + 1 : ℕ) : ℚ)) ^ 2 * aperyDeformationCoefficient n 0 t := by
  have h := congrArg (PowerSeries.coeff 0) (aperyDeformationSeries_step n t hshift)
  simpa [aperyDeformationCoefficient, add_mul, PowerSeries.coeff_C_mul] using h

theorem aperyDeformationCoefficient_step_succ (n m : ℕ) (t : ℚ)
    (hshift : t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    (t + ((n + 1 : ℕ) : ℚ)) ^ 2 *
        aperyDeformationCoefficient (n + 1) (m + 1) t +
      aperyDeformationCoefficient (n + 1) m t =
      (t - ((n + 1 : ℕ) : ℚ)) ^ 2 * aperyDeformationCoefficient n (m + 1) t := by
  have h := congrArg (PowerSeries.coeff (m + 1))
    (aperyDeformationSeries_step n t hshift)
  simpa only [aperyDeformationCoefficient, add_mul, map_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] using h

noncomputable def aperyDeformationGeneratingSeries (m : ℕ) (t : ℚ) :
    PowerSeries ℚ :=
  sequencePowerSeries (fun n => aperyDeformationCoefficient n m t)

noncomputable def aperyBaseOperator (t : ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  eulerShiftPowerSeries t (eulerShiftPowerSeries t f) -
    PowerSeries.X * eulerShiftPowerSeries (1 - t)
      (eulerShiftPowerSeries (1 - t) f)

theorem coeff_aperyBaseOperator_zero (t : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (aperyBaseOperator t f) =
      t ^ 2 * PowerSeries.coeff 0 f := by
  rw [aperyBaseOperator, map_sub, coeff_eulerShiftPowerSeries_sq]
  simp only [Nat.cast_zero, zero_add, PowerSeries.coeff_zero_X_mul, sub_zero]

theorem coeff_aperyBaseOperator_succ (t : ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (aperyBaseOperator t f) =
      (t + ((n + 1 : ℕ) : ℚ)) ^ 2 * PowerSeries.coeff (n + 1) f -
        (t - ((n + 1 : ℕ) : ℚ)) ^ 2 * PowerSeries.coeff n f := by
  rw [aperyBaseOperator, map_sub, coeff_eulerShiftPowerSeries_sq,
    PowerSeries.coeff_succ_X_mul, coeff_eulerShiftPowerSeries_sq]
  push_cast
  ring

theorem aperyDeformationGeneratingSeries_base (t : ℚ) (ht : t ≠ 0)
    (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    aperyBaseOperator t (aperyDeformationGeneratingSeries 0 t) = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      rw [coeff_aperyBaseOperator_zero]
      simp [aperyDeformationGeneratingSeries, aperyDeformationCoefficient,
        aperyDeformationSeries, quadraticInverseSeries]
      field_simp [ht]
  | succ n =>
      rw [coeff_aperyBaseOperator_succ]
      simp only [aperyDeformationGeneratingSeries, coeff_sequencePowerSeries]
      have h := aperyDeformationCoefficient_step_zero n t (hshift n)
      simpa using sub_eq_zero.mpr h

theorem aperyDeformationGeneratingSeries_extension (m : ℕ) (t : ℚ)
    (ht : t ≠ 0) (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    aperyBaseOperator t (aperyDeformationGeneratingSeries (m + 1) t) =
      -aperyDeformationGeneratingSeries m t := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      rw [coeff_aperyBaseOperator_zero, map_neg]
      simp only [aperyDeformationGeneratingSeries, coeff_sequencePowerSeries,
        aperyDeformationCoefficient, aperyDeformationSeries]
      have h := quadraticInverseSeries_coefficient_step t ht m
      linarith
  | succ n =>
      rw [coeff_aperyBaseOperator_succ, map_neg]
      simp only [aperyDeformationGeneratingSeries, coeff_sequencePowerSeries]
      have h := aperyDeformationCoefficient_step_succ n m t (hshift n)
      linarith

theorem aperyBaseOperator_injective (t : ℚ) (ht : t ≠ 0)
    (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    Function.Injective (aperyBaseOperator t) := by
  intro f g h
  apply PowerSeries.ext
  intro n
  induction n with
  | zero =>
      have hc := congrArg (PowerSeries.coeff 0) h
      rw [coeff_aperyBaseOperator_zero, coeff_aperyBaseOperator_zero] at hc
      exact mul_left_cancel₀ (pow_ne_zero 2 ht) hc
  | succ n ih =>
      have hc := congrArg (PowerSeries.coeff (n + 1)) h
      rw [coeff_aperyBaseOperator_succ, coeff_aperyBaseOperator_succ, ih] at hc
      have hc' := sub_left_inj.mp hc
      exact mul_left_cancel₀ (pow_ne_zero 2 (hshift n)) hc'

theorem aperyDeformationTower_unique (t : ℚ) (ht : t ≠ 0)
    (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0)
    (F : ℕ → PowerSeries ℚ)
    (hbase : aperyBaseOperator t (F 0) = 1)
    (hext : ∀ m, aperyBaseOperator t (F (m + 1)) = -F m) :
    ∀ m, F m = aperyDeformationGeneratingSeries m t := by
  intro m
  induction m with
  | zero =>
      apply aperyBaseOperator_injective t ht hshift
      rw [hbase, aperyDeformationGeneratingSeries_base t ht hshift]
  | succ m ih =>
      apply aperyBaseOperator_injective t ht hshift
      rw [hext m, aperyDeformationGeneratingSeries_extension m t ht hshift, ih]

noncomputable def aperyDeformationDenominator (n : ℕ) (t : ℚ) : PowerSeries ℚ :=
  ∏ j ∈ Finset.range (n + 1),
    (PowerSeries.C ((t + (j : ℚ)) ^ 2) + PowerSeries.X)

theorem aperyDeformationSeries_denominator_identity (n : ℕ) (t : ℚ)
    (hnonzero : ∀ j : ℕ, t + (j : ℚ) ≠ 0) :
    aperyDeformationDenominator n t * aperyDeformationSeries n t =
      PowerSeries.C ((aperyNumerator n t) ^ 2) := by
  induction n with
  | zero =>
      simpa [aperyDeformationDenominator, aperyDeformationSeries,
        aperyNumerator] using quadraticInverseSeries_cancel t (by simpa using hnonzero 0)
  | succ n ih =>
      have hden : aperyDeformationDenominator (n + 1) t =
          aperyDeformationDenominator n t *
            (PowerSeries.C ((t + ((n + 1 : ℕ) : ℚ)) ^ 2) + PowerSeries.X) := by
        simp only [aperyDeformationDenominator, Finset.prod_range_succ]
      rw [hden]
      calc
        _ = aperyDeformationDenominator n t *
            ((PowerSeries.C ((t + ((n + 1 : ℕ) : ℚ)) ^ 2) + PowerSeries.X) *
              aperyDeformationSeries (n + 1) t) := by ring
        _ = aperyDeformationDenominator n t *
            (PowerSeries.C ((t - ((n + 1 : ℕ) : ℚ)) ^ 2) *
              aperyDeformationSeries n t) := by
                rw [aperyDeformationSeries_step n t (hnonzero (n + 1))]
        _ = PowerSeries.C ((t - ((n + 1 : ℕ) : ℚ)) ^ 2) *
            (aperyDeformationDenominator n t * aperyDeformationSeries n t) := by ring
        _ = _ := by
          rw [ih, aperyNumerator_succ, mul_pow, map_mul]
          ring

theorem aperyDeformationDenominator_constantCoeff (n : ℕ) (t : ℚ) :
    PowerSeries.constantCoeff (aperyDeformationDenominator n t) =
      (aperyDenominator n t) ^ 2 := by
  simp [aperyDeformationDenominator, aperyDenominator, ← Finset.prod_pow]

theorem aperyDeformationCoefficient_zero (n : ℕ) (t : ℚ)
    (hnonzero : ∀ j : ℕ, t + (j : ℚ) ≠ 0) :
    aperyDeformationCoefficient n 0 t = aperyF n t := by
  have hden : aperyDenominator n t ≠ 0 := by
    unfold aperyDenominator
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hnonzero j)
  have hc := congrArg PowerSeries.constantCoeff
    (aperyDeformationSeries_denominator_identity n t hnonzero)
  change PowerSeries.coeff 0 (aperyDeformationSeries n t) = _
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold aperyF
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hden)).2
  simpa only [map_mul, aperyDeformationDenominator_constantCoeff,
    PowerSeries.constantCoeff_C, mul_comm] using hc

theorem aperyDeformationSeries_unique (n : ℕ) (t : ℚ)
    (hnonzero : ∀ j : ℕ, t + (j : ℚ) ≠ 0) (f : PowerSeries ℚ)
    (hf : aperyDeformationDenominator n t * f =
      PowerSeries.C ((aperyNumerator n t) ^ 2)) :
    f = aperyDeformationSeries n t := by
  have hden : aperyDenominator n t ≠ 0 := by
    unfold aperyDenominator
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hnonzero j)
  have hseriesden : aperyDeformationDenominator n t ≠ 0 := by
    intro hzero
    have hc := congrArg PowerSeries.constantCoeff hzero
    rw [aperyDeformationDenominator_constantCoeff, map_zero] at hc
    exact pow_ne_zero 2 hden hc
  apply mul_left_cancel₀ hseriesden
  rw [hf, aperyDeformationSeries_denominator_identity n t hnonzero]

def aperyQuadraticDenominator (n : ℕ) (t z : ℚ) : ℚ :=
  ∏ j ∈ Finset.range (n + 1), ((t + (j : ℚ)) ^ 2 + z)

theorem aperyQuadraticDenominator_succ (n : ℕ) (t z : ℚ) :
    aperyQuadraticDenominator (n + 1) t z =
      aperyQuadraticDenominator n t z *
        ((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z) := by
  simp only [aperyQuadraticDenominator, Finset.prod_range_succ]

theorem aperyR_quadratic_denominator_identity (n : ℕ) (t z : ℚ)
    (hshift : ∀ j : ℕ, t + (j : ℚ) ≠ 0)
    (hquad : ∀ j : ℕ, (t + (j : ℚ)) ^ 2 + z ≠ 0) :
    aperyR n t z * aperyQuadraticDenominator n t z =
      (aperyNumerator n t) ^ 2 := by
  have hden (k : ℕ) : aperyDenominator k t ≠ 0 := by
    unfold aperyDenominator
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hshift j)
  induction n with
  | zero =>
      have ht : t ≠ 0 := by simpa using hshift 0
      have hz : t ^ 2 + z ≠ 0 := by simpa using hquad 0
      rw [aperyR_zero_closed_form t z ht hz]
      simp [aperyQuadraticDenominator, aperyNumerator, hz]
  | succ n ih =>
      rw [aperyR_succ_ratio n t z (hden n) (hshift (n + 1)) (hquad (n + 1)),
        aperyQuadraticDenominator_succ, aperyNumerator_succ]
      calc
        _ = (aperyR n t z * aperyQuadraticDenominator n t z) *
            (t - ((n + 1 : ℕ) : ℚ)) ^ 2 := by
              calc
                _ = (aperyR n t z * aperyQuadraticDenominator n t z) *
                    (((t - ((n + 1 : ℕ) : ℚ)) ^ 2 /
                      ((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z)) *
                        ((t + ((n + 1 : ℕ) : ℚ)) ^ 2 + z)) := by ring
                _ = _ := by rw [div_mul_cancel₀ _ (hquad (n + 1))]
        _ = _ := by rw [ih]; ring

theorem aperyBaseOperator_add (t : ℚ) (f g : PowerSeries ℚ) :
    aperyBaseOperator t (f + g) = aperyBaseOperator t f + aperyBaseOperator t g := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [coeff_aperyBaseOperator_zero, map_add]; ring
  | succ n => simp only [coeff_aperyBaseOperator_succ, map_add]; ring

theorem aperyBaseOperator_smul (t c : ℚ) (f : PowerSeries ℚ) :
    aperyBaseOperator t (c • f) = c • aperyBaseOperator t f := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp only [coeff_aperyBaseOperator_zero, PowerSeries.coeff_smul, smul_eq_mul]
      ring
  | succ n =>
      simp only [coeff_aperyBaseOperator_succ, PowerSeries.coeff_smul, smul_eq_mul]
      ring

noncomputable def aperySourceLiftCoefficient (t : ℚ) (source : PowerSeries ℚ) :
    ℕ → ℚ
  | 0 => PowerSeries.coeff 0 source / t ^ 2
  | n + 1 =>
      (PowerSeries.coeff (n + 1) source +
        (t - ((n + 1 : ℕ) : ℚ)) ^ 2 * aperySourceLiftCoefficient t source n) /
          (t + ((n + 1 : ℕ) : ℚ)) ^ 2

noncomputable def aperySourceLift (t : ℚ) (source : PowerSeries ℚ) :
    PowerSeries ℚ := PowerSeries.mk (aperySourceLiftCoefficient t source)

theorem aperySourceLift_equation (t : ℚ) (ht : t ≠ 0)
    (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0)
    (source : PowerSeries ℚ) :
    aperyBaseOperator t (aperySourceLift t source) = source := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      rw [coeff_aperyBaseOperator_zero]
      simp only [aperySourceLift, PowerSeries.coeff_mk, aperySourceLiftCoefficient]
      field_simp [ht]
  | succ n =>
      rw [coeff_aperyBaseOperator_succ]
      simp only [aperySourceLift, PowerSeries.coeff_mk, aperySourceLiftCoefficient]
      rw [mul_div_cancel₀ _ (pow_ne_zero 2 (hshift n))]
      ring

noncomputable def aperySourceLiftLinear (t : ℚ) (ht : t ≠ 0)
    (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    PowerSeries ℚ →ₗ[ℚ] PowerSeries ℚ where
  toFun := aperySourceLift t
  map_add' f g := by
    apply aperyBaseOperator_injective t ht hshift
    rw [aperySourceLift_equation t ht hshift, aperyBaseOperator_add,
      aperySourceLift_equation t ht hshift, aperySourceLift_equation t ht hshift]
  map_smul' c f := by
    apply aperyBaseOperator_injective t ht hshift
    rw [aperySourceLift_equation t ht hshift, aperyBaseOperator_smul,
      aperySourceLift_equation t ht hshift]
    rfl

theorem aperySourceLift_left_inverse (t : ℚ) (ht : t ≠ 0)
    (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0) (f : PowerSeries ℚ) :
    aperySourceLiftLinear t ht hshift (aperyBaseOperator t f) = f := by
  apply aperyBaseOperator_injective t ht hshift
  exact aperySourceLift_equation t ht hshift (aperyBaseOperator t f)

theorem aperyDeformationGeneratingSeries_inducedLift (m : ℕ) (t : ℚ)
    (ht : t ≠ 0) (hshift : ∀ n, t + ((n + 1 : ℕ) : ℚ) ≠ 0) :
    aperyDeformationGeneratingSeries (m + 1) t =
      aperySourceLiftLinear t ht hshift (-aperyDeformationGeneratingSeries m t) := by
  apply aperyBaseOperator_injective t ht hshift
  change aperyBaseOperator t (aperyDeformationGeneratingSeries (m + 1) t) =
    aperyBaseOperator t (aperySourceLift t (-aperyDeformationGeneratingSeries m t))
  rw [aperyDeformationGeneratingSeries_extension m t ht hshift,
    aperySourceLift_equation t ht hshift]

end OddZeta
