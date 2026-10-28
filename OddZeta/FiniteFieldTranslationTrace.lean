import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Linarith

namespace OddZeta

noncomputable def polynomialTranslationTrace {K : Type*} [Field K] [Fintype K]
    (P : Polynomial K) : Polynomial K := ∑ a : K, Polynomial.taylor a P

theorem finite_field_sum_eval_zero {K : Type*} [Field K] [Fintype K]
    (P : Polynomial K) (hdegree : P.natDegree < Fintype.card K - 1) :
    ∑ a : K, P.eval a = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← Finset.mul_sum]
  have hjlt : j < Fintype.card K - 1 := by
    have h := Finset.mem_range.mp hj
    omega
  rw [FiniteField.sum_pow_lt_card_sub_one K j hjlt, mul_zero]

theorem translation_trace_coefficient {K : Type*} [Field K] [Fintype K]
    (P : Polynomial K) (k : ℕ) :
    (polynomialTranslationTrace P).coeff k =
      ∑ a : K, (Polynomial.hasseDeriv k P).eval a := by
  classical
  simp [polynomialTranslationTrace, Polynomial.taylor_coeff]

theorem translation_trace_coefficient_vanishes {K : Type*} [Field K] [Fintype K]
    (P : Polynomial K) (k : ℕ)
    (hdegree : P.natDegree < k + (Fintype.card K - 1)) :
    (polynomialTranslationTrace P).coeff k = 0 := by
  rw [translation_trace_coefficient]
  by_cases hk : P.natDegree < k
  · rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree P k hk]
    simp
  · apply finite_field_sum_eval_zero
    have hbound := Polynomial.natDegree_hasseDeriv_le P k
    omega

theorem translation_trace_small_polynomial_zero {K : Type*} [Field K] [Fintype K]
    (P : Polynomial K) (hdegree : P.natDegree < Fintype.card K - 1) :
    polynomialTranslationTrace P = 0 := by
  ext k
  rw [Polynomial.coeff_zero]
  apply translation_trace_coefficient_vanishes
  omega

theorem translation_trace_composition_coefficient_vanishes
    {K : Type*} [Field K] [Fintype K]
    (P R F : Polynomial K) (k : ℕ) (hk : 0 < k) (hF : 0 < F.natDegree)
    (hidentify : polynomialTranslationTrace P = R.comp F)
    (hdegree : P.natDegree < k * F.natDegree + (Fintype.card K - 1)) :
    R.coeff k = 0 := by
  by_contra hcoeff
  have hknat := Polynomial.le_natDegree_of_ne_zero hcoeff
  have htrace : (polynomialTranslationTrace P).natDegree =
      R.natDegree * F.natDegree := by
    rw [hidentify, Polynomial.natDegree_comp]
  have hj : k * F.natDegree ≤ R.natDegree * F.natDegree :=
    Nat.mul_le_mul_right F.natDegree hknat
  have hjpos : 0 < R.natDegree * F.natDegree :=
    (Nat.mul_pos hk hF).trans_le hj
  have hnonzero : polynomialTranslationTrace P ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at htrace
    omega
  have hvan := translation_trace_coefficient_vanishes P
    (R.natDegree * F.natDegree) (by omega)
  have hlead := Polynomial.leadingCoeff_ne_zero.mpr hnonzero
  rw [Polynomial.leadingCoeff, htrace, hvan] at hlead
  exact hlead rfl

theorem translation_trace_pade_degree_inequality (s n m p k : ℤ)
    (hs : 2 ≤ s) (hm : m ≤ n)
    (hinterval : (k - 1) * p ≤ (s - 2) * n) :
    (s - 1) * p + 2 * m - s * n - s + 1 < (s - k) * p := by
  nlinarith

end OddZeta
