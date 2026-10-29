import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OddZeta

theorem integer_adjugate_vector_image {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℤ) (x : n → ℤ) :
    B.mulVec (B.adjugate.mulVec x) = fun i => B.det * x i := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
  funext i
  simp

theorem integer_det_row_envelope {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (H : n → ℤ) (hA : ∀ i j, |A i j| ≤ H i) :
    |A.det| ≤ (Fintype.card n).factorial * ∏ i, H i := by
  let abv : AbsoluteValue ℤ ℤ := AbsoluteValue.abs
  change abv A.det ≤ _
  calc
    abv A.det = abv (∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i) := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm n, abv (Equiv.Perm.sign σ • ∏ i, A (σ i) i) :=
      abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ σ : Equiv.Perm n, ∏ i, H (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Fintype.card n).factorial * ∏ i, H i := by
      simp only [Equiv.prod_comp, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, nsmul_eq_mul]

theorem integer_cramer_row_envelope {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (b H : n → ℤ)
    (hA : ∀ i j, |A i j| ≤ H i) (hb : ∀ i, |b i| ≤ H i) (j : n) :
    |Matrix.cramer A b j| ≤ (Fintype.card n).factorial * ∏ i, H i := by
  rw [Matrix.cramer_apply]
  apply integer_det_row_envelope
  intro i k
  by_cases hk : k = j
  · subst k
    simpa [Matrix.updateCol] using hb i
  · simpa [Matrix.updateCol, hk] using hA i k

theorem integer_cramer_cancellation {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (b : n → ℤ) (i : n) :
    (∑ j, A i j * (-Matrix.cramer A b j)) + b i * A.det = 0 := by
  have h := congrFun (Matrix.mulVec_cramer A b) i
  change (∑ j, A i j * Matrix.cramer A b j) = A.det * b i at h
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib, h]
  ring

theorem integer_cramer_mass_envelope {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (b H : n → ℤ)
    (hA : ∀ i j, |A i j| ≤ H i) (hb : ∀ i, |b i| ≤ H i) :
    (∑ j, |-Matrix.cramer A b j|) + |A.det| ≤
      (Fintype.card n + 1) * ((Fintype.card n).factorial * ∏ i, H i) := by
  have hs : (∑ j, |-Matrix.cramer A b j|) ≤
      Fintype.card n * ((Fintype.card n).factorial * ∏ i, H i) := by
    calc
      _ ≤ ∑ _j : n, ((Fintype.card n).factorial * ∏ i, H i) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [abs_neg] using integer_cramer_row_envelope A b H hA hb j
      _ = _ := by simp
  have hd := integer_det_row_envelope A H hA
  nlinarith

theorem integer_two_free_coordinates_independent (delta u v : ℤ)
    (hdelta : delta ≠ 0) (hu : u * delta = 0) (hv : v * delta = 0) :
    u = 0 ∧ v = 0 := by
  exact ⟨(mul_eq_zero.mp hu).resolve_right hdelta,
    (mul_eq_zero.mp hv).resolve_right hdelta⟩

end OddZeta
