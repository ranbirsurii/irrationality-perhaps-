import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Convert

namespace OddZeta

def arithmeticMatrixShift {R : Type*} [CommRing R] {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (x : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j => x + H i j

theorem det_arithmeticMatrixShift_affine {R : Type*} [CommRing R] {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (x : R) :
    (arithmeticMatrixShift H x).det =
      ((arithmeticMatrixShift H 1).det - (arithmeticMatrixShift H 0).det) * x +
        (arithmeticMatrixShift H 0).det := by
  classical
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    fun i j => if i = 0 then H 0 j else H i j - H 0 j
  have hd (y : R) : (Matrix.updateRow B 0 (fun j => y + H 0 j)).det =
      (arithmeticMatrixShift H y).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 0 then 0 else -1) 0 (by simp)
    intro i j
    by_cases hi : i = 0
    · subst i
      simp [Matrix.updateRow, arithmeticMatrixShift]
      rw [Function.update_self]
    · simp [Matrix.updateRow, arithmeticMatrixShift, B, hi]
      ring
  have hf (y : R) : (arithmeticMatrixShift H y).det =
      y * (Matrix.updateRow B 0 (fun _ => 1)).det +
        (Matrix.updateRow B 0 (fun j => H 0 j)).det := by
    rw [← hd y]
    have hrow : (fun j => y + H 0 j) =
        y • (fun _ => (1 : R)) + (fun j => H 0 j) := by
      funext j
      simp
    rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  rw [hf x, hf 1, hf 0]
  ring

theorem arithmeticIntegerEventuallyZero (u : ℕ → ℤ)
    (hlim : Filter.Tendsto (fun n => (u n : ℝ)) Filter.atTop (nhds 0)) :
    ∃ N, ∀ n ≥ N, u n = 0 := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) 1 (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have h : |(u n : ℝ)| < 1 := by
    simpa [Real.dist_eq] using hN n hn
  have hb := abs_lt.mp h
  have hl : (-1 : ℤ) < u n := by exact_mod_cast hb.1
  have hu : u n < 1 := by exact_mod_cast hb.2
  omega

theorem arithmeticIrrationalOfSmallForms (α : ℝ) (A B : ℕ → ℤ)
    (hsmall : Filter.Tendsto (fun n => (A n : ℝ) * α - (B n : ℝ))
      Filter.atTop (nhds 0))
    (hnonzero : ∀ N, ∃ n ≥ N, (A n : ℝ) * α - (B n : ℝ) ≠ 0) :
    Irrational α := by
  rw [irrational_iff_ne_rational]
  intro p d hd hα
  let u : ℕ → ℤ := fun n => p * A n - d * B n
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have heq (n : ℕ) : (u n : ℝ) =
      (d : ℝ) * ((A n : ℝ) * α - (B n : ℝ)) := by
    dsimp [u]
    rw [hα]
    push_cast
    field_simp [hdR]
  have hlim : Filter.Tendsto (fun n => (u n : ℝ)) Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.const_mul (d : ℝ) hsmall
    simpa only [mul_zero, ← heq] using h
  obtain ⟨N, hN⟩ := arithmeticIntegerEventuallyZero u hlim
  obtain ⟨n, hn, hne⟩ := hnonzero N
  have hz : (u n : ℝ) = 0 := by exact_mod_cast hN n hn
  rw [heq] at hz
  exact (mul_ne_zero hdR hne) hz

noncomputable def arithmeticOddZetaValue (r : ℕ) : ℝ :=
  (riemannZeta ((2 * r + 1 : ℕ) : ℂ)).re

def harmonicPower (s m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range m, 1 / ((j + 1 : ℕ) : ℚ) ^ s

def harmonicLcm (M : ℕ) : ℕ :=
  (Finset.range M).lcm (fun j => j + 1)

theorem harmonicLcm_ne_zero (M : ℕ) : harmonicLcm M ≠ 0 := by
  apply Finset.lcm_ne_zero_iff.mpr
  intro j hj
  omega

theorem successor_dvd_harmonicLcm {j M : ℕ} (hj : j < M) :
    j + 1 ∣ harmonicLcm M :=
  Finset.dvd_lcm (Finset.mem_range.mpr hj)

theorem harmonicLcm_eq_lcmUpto (M : ℕ) : harmonicLcm M = Nat.lcmUpto M := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro j hj
    exact Finset.dvd_lcm (s := Finset.Icc 1 M) (f := id)
      (Finset.mem_Icc.mpr ⟨by omega, by have h := Finset.mem_range.mp hj; omega⟩)
  · apply Finset.lcm_dvd
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hd := successor_dvd_harmonicLcm (j := j - 1) (M := M) (by omega)
    simpa [Nat.sub_add_cancel hj'.1] using hd

theorem harmonicLcm_binomial_bound (M : ℕ) :
    2 ^ M ≤ (M + 1) * harmonicLcm M := by
  rw [harmonicLcm_eq_lcmUpto]
  exact Chebyshev.two_pow_le_mul_lcmUpto M

theorem harmonicLcm_log_lower (M : ℕ) :
    (M : ℝ) * Real.log 2 - Real.log (M + 1 : ℕ) ≤
      Real.log (harmonicLcm M : ℝ) := by
  have hd : (0 : ℝ) < (harmonicLcm M : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (harmonicLcm_ne_zero M)
  have hbound : (2 : ℝ) ^ M ≤ (M + 1 : ℕ) * (harmonicLcm M : ℝ) := by
    exact_mod_cast harmonicLcm_binomial_bound M
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ M) hbound
  rw [Real.log_pow, Real.log_mul (by positivity) hd.ne'] at hlog
  linarith

def scaledHarmonicPower (s M m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range m, ((harmonicLcm M / (j + 1)) ^ s : ℕ)

theorem scaledHarmonicPower_cast (s M m : ℕ) (hm : m ≤ M) :
    (scaledHarmonicPower s M m : ℚ) =
      (harmonicLcm M : ℚ) ^ s * harmonicPower s m := by
  unfold scaledHarmonicPower harmonicPower
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_natCast, Nat.cast_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hd := successor_dvd_harmonicLcm
    (lt_of_lt_of_le (Finset.mem_range.mp hj) hm)
  have hq : (harmonicLcm M / (j + 1) : ℕ) * (j + 1) = harmonicLcm M :=
    Nat.div_mul_cancel hd
  have hqQ : ((harmonicLcm M / (j + 1) : ℕ) : ℚ) * (j + 1 : ℕ) =
      (harmonicLcm M : ℚ) := by exact_mod_cast hq
  have hne : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have heq : ((harmonicLcm M / (j + 1) : ℕ) : ℚ) =
      (harmonicLcm M : ℚ) / ((j + 1 : ℕ) : ℚ) :=
    (eq_div_iff hne).mpr hqQ
  rw [heq, div_pow]
  ring

theorem det_arithmeticMatrixShift_scaled_affine {R : Type*} [CommRing R] {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (d x : R) :
    (arithmeticMatrixShift H (d * x)).det =
      ((arithmeticMatrixShift H d).det - (arithmeticMatrixShift H 0).det) * x +
        (arithmeticMatrixShift H 0).det := by
  rw [det_arithmeticMatrixShift_affine H (d * x),
    det_arithmeticMatrixShift_affine H d]
  ring

def oddHankelBase (s n a : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i j => -harmonicPower s (a + i.val + j.val)

def oddHankelEntryScale (s n a : ℕ) : ℕ :=
  harmonicLcm (a + 2 * n) ^ s

def oddHankelIntegerBase (s n a : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => -scaledHarmonicPower s (a + 2 * n) (a + i.val + j.val)

noncomputable def oddHankelIntegerA (s n a : ℕ) : ℤ :=
  (arithmeticMatrixShift (oddHankelIntegerBase s n a)
    (oddHankelEntryScale s n a : ℤ)).det -
      (arithmeticMatrixShift (oddHankelIntegerBase s n a) 0).det

noncomputable def oddHankelIntegerB (s n a : ℕ) : ℤ :=
  (arithmeticMatrixShift (oddHankelIntegerBase s n a) 0).det

theorem oddHankelEntryScale_ne_zero (s n a : ℕ) :
    oddHankelEntryScale s n a ≠ 0 :=
  pow_ne_zero _ (harmonicLcm_ne_zero _)

theorem oddHankel_arithmetic_prime_cost (s n a p : ℕ) (hp : p.Prime) :
    ((oddHankelEntryScale s n a) ^ (n + 1)).factorization p =
      s * (n + 1) * Nat.log p (a + 2 * n) := by
  simp [oddHankelEntryScale, harmonicLcm_eq_lcmUpto, Nat.factorization_pow,
    Nat.factorization_lcmUpto _ hp, mul_assoc, mul_comm, mul_left_comm]

theorem arithmetic_basis_change_determinant {R : Type*} [CommRing R] {n : ℕ}
    (M T : Matrix (Fin n) (Fin n) R) :
    (T.transpose * M * T).det = T.det ^ 2 * M.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem oddHankel_arithmetic_log_cost (s n a : ℕ) :
    (s : ℝ) * (n + 1 : ℕ) *
      ((a + 2 * n : ℕ) * Real.log 2 - Real.log (a + 2 * n + 1 : ℕ)) ≤
      Real.log ((oddHankelEntryScale s n a : ℝ) ^ (n + 1)) := by
  have h := mul_le_mul_of_nonneg_left (harmonicLcm_log_lower (a + 2 * n))
    (show (0 : ℝ) ≤ (s : ℝ) * (n + 1 : ℕ) by positivity)
  simpa [oddHankelEntryScale, Real.log_pow, mul_assoc, mul_comm, mul_left_comm]
    using h

theorem oddHankelIntegerBase_cast (s n a : ℕ) :
    (oddHankelIntegerBase s n a).map (Int.castRingHom ℚ) =
      (oddHankelEntryScale s n a : ℚ) • oddHankelBase s n a := by
  ext i j
  have hm : a + i.val + j.val ≤ a + 2 * n := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  change -(scaledHarmonicPower s (a + 2 * n) (a + i.val + j.val) : ℚ) =
    (oddHankelEntryScale s n a : ℚ) * -harmonicPower s (a + i.val + j.val)
  rw [scaledHarmonicPower_cast s _ _ hm]
  simp only [oddHankelEntryScale, Nat.cast_pow]
  ring

theorem oddHankel_integer_linear_form (s n a : ℕ) (x : ℝ) :
    (oddHankelEntryScale s n a : ℝ) ^ (n + 1) *
      Matrix.det (fun i j : Fin (n + 1) =>
        x - (harmonicPower s (a + i.val + j.val) : ℝ)) =
      (oddHankelIntegerA s n a : ℝ) * x +
        (oddHankelIntegerB s n a : ℝ) := by
  let Z := oddHankelIntegerBase s n a
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => -(harmonicPower s (a + i.val + j.val) : ℝ)
  let d : ℝ := oddHankelEntryScale s n a
  have hZ : Z.map (Int.castRingHom ℝ) = d • H := by
    ext i j
    have hm : a + i.val + j.val ≤ a + 2 * n := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    have h := scaledHarmonicPower_cast s (a + 2 * n) (a + i.val + j.val) hm
    have hR : (scaledHarmonicPower s (a + 2 * n) (a + i.val + j.val) : ℝ) =
        (harmonicLcm (a + 2 * n) : ℝ) ^ s *
          (harmonicPower s (a + i.val + j.val) : ℝ) := by exact_mod_cast h
    simp only [Z, Matrix.map_apply, oddHankelIntegerBase, map_neg, H]
    change -(scaledHarmonicPower s (a + 2 * n) (a + i.val + j.val) : ℝ) =
      d * -(harmonicPower s (a + i.val + j.val) : ℝ)
    rw [hR]
    simp [d, oddHankelEntryScale, mul_neg]
  have hc (y : ℤ) :
      (((arithmeticMatrixShift Z y).det : ℤ) : ℝ) =
        (arithmeticMatrixShift (d • H) (y : ℝ)).det := by
    change (Int.castRingHom ℝ) ((arithmeticMatrixShift Z y).det) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    have hz := congrArg (fun M => M i j) hZ
    simpa [arithmeticMatrixShift] using congrArg (fun z : ℝ => (y : ℝ) + z) hz
  have hs : d • arithmeticMatrixShift H x =
      arithmeticMatrixShift (d • H) (d * x) := by
    ext i j
    simp [arithmeticMatrixShift, mul_add]
  have hf := det_arithmeticMatrixShift_scaled_affine (d • H) d x
  rw [← hs, Matrix.det_smul] at hf
  simp only [Fintype.card_fin] at hf
  have hcD := hc (oddHankelEntryScale s n a : ℤ)
  have hc0 := hc 0
  simp only [Int.cast_natCast, Int.cast_zero] at hcD hc0
  rw [← hcD, ← hc0] at hf
  convert! hf using 1
  simp [oddHankelIntegerA, oddHankelIntegerB, Z, sub_eq_add_neg]

theorem oddHankel_divided_integer_linear_form (s n a : ℕ) (g : ℤ)
    (hg : g ≠ 0) (hA : g ∣ oddHankelIntegerA s n a)
    (hB : g ∣ oddHankelIntegerB s n a) (x : ℝ) :
    (oddHankelEntryScale s n a : ℝ) ^ (n + 1) / (g : ℝ) *
      Matrix.det (fun i j : Fin (n + 1) =>
        x - (harmonicPower s (a + i.val + j.val) : ℝ)) =
      ((oddHankelIntegerA s n a / g : ℤ) : ℝ) * x +
        ((oddHankelIntegerB s n a / g : ℤ) : ℝ) := by
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  have ha : ((oddHankelIntegerA s n a / g : ℤ) : ℝ) * (g : ℝ) =
      (oddHankelIntegerA s n a : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hA
  have hb : ((oddHankelIntegerB s n a / g : ℤ) : ℝ) * (g : ℝ) =
      (oddHankelIntegerB s n a : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hB
  rw [div_mul_eq_mul_div, div_eq_iff hgR, oddHankel_integer_linear_form,
    ← ha, ← hb]
  ring

theorem oddHankel_gcd_integer_linear_form (s n a : ℕ)
    (hg : Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) ≠ 0)
    (x : ℝ) :
    (oddHankelEntryScale s n a : ℝ) ^ (n + 1) /
      (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℝ) *
      Matrix.det (fun i j : Fin (n + 1) =>
        x - (harmonicPower s (a + i.val + j.val) : ℝ)) =
      ((oddHankelIntegerA s n a /
        (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ) : ℤ) : ℝ) * x +
      ((oddHankelIntegerB s n a /
        (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ) : ℤ) : ℝ) := by
  simpa only [Int.cast_natCast] using
    oddHankel_divided_integer_linear_form s n a
      (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ)
      (by exact_mod_cast hg) (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _) x

theorem oddHankel_irrational_of_divided_decay (r : ℕ) (a : ℕ → ℕ)
    (g : ℕ → ℤ) (hg : ∀ n, g n ≠ 0)
    (hA : ∀ n, g n ∣ oddHankelIntegerA (2 * r + 1) n (a n))
    (hB : ∀ n, g n ∣ oddHankelIntegerB (2 * r + 1) n (a n))
    (hsmall : Filter.Tendsto
      (fun n => (oddHankelEntryScale (2 * r + 1) n (a n) : ℝ) ^ (n + 1) /
        (g n : ℝ) * Matrix.det (fun i j : Fin (n + 1) => arithmeticOddZetaValue r -
          (harmonicPower (2 * r + 1) (a n + i.val + j.val) : ℝ)))
      Filter.atTop (nhds 0))
    (hnonzero : ∀ N, ∃ n ≥ N,
      Matrix.det (fun i j : Fin (n + 1) => arithmeticOddZetaValue r -
        (harmonicPower (2 * r + 1) (a n + i.val + j.val) : ℝ)) ≠ 0) :
    Irrational (arithmeticOddZetaValue r) := by
  apply arithmeticIrrationalOfSmallForms (arithmeticOddZetaValue r)
    (fun n => oddHankelIntegerA (2 * r + 1) n (a n) / g n)
    (fun n => -(oddHankelIntegerB (2 * r + 1) n (a n) / g n))
  · simpa only [Int.cast_neg, sub_neg_eq_add,
      ← oddHankel_divided_integer_linear_form _ _ _ _ (hg _) (hA _) (hB _)] using hsmall
  · intro N
    obtain ⟨n, hn, hdet⟩ := hnonzero N
    refine ⟨n, hn, ?_⟩
    rw [Int.cast_neg, sub_neg_eq_add,
      ← oddHankel_divided_integer_linear_form _ _ _ _ (hg n) (hA n) (hB n)]
    exact mul_ne_zero (div_ne_zero (pow_ne_zero _ (by
      exact_mod_cast oddHankelEntryScale_ne_zero (2 * r + 1) n (a n)))
        (by exact_mod_cast hg n)) hdet

theorem oddHankel_irrational_of_cleared_decay (r : ℕ) (a : ℕ → ℕ)
    (hsmall : Filter.Tendsto
      (fun n => (oddHankelEntryScale (2 * r + 1) n (a n) : ℝ) ^ (n + 1) *
        Matrix.det (fun i j : Fin (n + 1) => arithmeticOddZetaValue r -
          (harmonicPower (2 * r + 1) (a n + i.val + j.val) : ℝ)))
      Filter.atTop (nhds 0))
    (hnonzero : ∀ N, ∃ n ≥ N,
      Matrix.det (fun i j : Fin (n + 1) => arithmeticOddZetaValue r -
        (harmonicPower (2 * r + 1) (a n + i.val + j.val) : ℝ)) ≠ 0) :
    Irrational (arithmeticOddZetaValue r) := by
  apply arithmeticIrrationalOfSmallForms (arithmeticOddZetaValue r)
    (fun n => oddHankelIntegerA (2 * r + 1) n (a n))
    (fun n => -oddHankelIntegerB (2 * r + 1) n (a n))
  · simpa only [Int.cast_one, Int.cast_neg, sub_neg_eq_add, one_mul,
      ← oddHankel_integer_linear_form] using hsmall
  · intro N
    obtain ⟨n, hn, hdet⟩ := hnonzero N
    refine ⟨n, hn, ?_⟩
    rw [Int.cast_neg, sub_neg_eq_add, ← oddHankel_integer_linear_form]
    exact mul_ne_zero (pow_ne_zero _ (by
      exact_mod_cast oddHankelEntryScale_ne_zero (2 * r + 1) n (a n))) hdet

end OddZeta
