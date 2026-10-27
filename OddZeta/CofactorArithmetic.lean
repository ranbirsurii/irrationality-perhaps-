import OddZeta.IntegralFramedComparison
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.GCDMonoid.Finset

namespace OddZeta

theorem det_updateRow_cofactor_expansion {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (i : Fin (n + 1))
    (v : Fin (n + 1) → ℤ) :
    (B.updateRow i v).det = ∑ j, v j * B.adjugate j i := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp [Matrix.mulVec, dotProduct, mul_comm]

def cofactorDifferenceBase {n : ℕ} (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => if i = 0 then Z 0 j else Z i j - Z 0 j

noncomputable def cofactorVector {n : ℕ} (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (j : Fin (n + 1)) : ℤ := (cofactorDifferenceBase Z).adjugate j 0

noncomputable def cofactorContent {n : ℕ}
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : ℤ :=
  Finset.univ.gcd (cofactorVector Z)

theorem cofactorContent_dvd {n : ℕ}
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (j : Fin (n + 1)) :
    cofactorContent Z ∣ cofactorVector Z j :=
  Finset.gcd_dvd (Finset.mem_univ j)

theorem affine_determinant_cofactor_expansion {n : ℕ}
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (x : ℤ) :
    (arithmeticMatrixShift Z x).det =
      x * (∑ j, cofactorVector Z j) + ∑ j, Z 0 j * cofactorVector Z j := by
  classical
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    fun i j => if i = 0 then Z 0 j else Z i j - Z 0 j
  have hd : (Matrix.updateRow B 0 (fun j => x + Z 0 j)).det =
      (arithmeticMatrixShift Z x).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 0 then 0 else -1) 0 (by simp)
    intro i j
    by_cases hi : i = 0
    · subst i
      simp [Matrix.updateRow, arithmeticMatrixShift]
      rw [Function.update_self]
    · simp [Matrix.updateRow, arithmeticMatrixShift, B, hi]
      ring
  rw [← hd, det_updateRow_cofactor_expansion]
  rw [show B = cofactorDifferenceBase Z from rfl]
  simp only [cofactorVector, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem cofactorContent_dvd_affine_determinant {n : ℕ}
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (x : ℤ) :
    cofactorContent Z ∣ (arithmeticMatrixShift Z x).det := by
  rw [affine_determinant_cofactor_expansion]
  apply dvd_add
  · apply dvd_mul_of_dvd_right
    exact Finset.dvd_sum (fun j _ => cofactorContent_dvd Z j)
  · exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_right (cofactorContent_dvd Z j) _)

theorem oddHankel_cofactor_content_divides (s n a : ℕ) :
    cofactorContent (oddHankelIntegerBase s n a) ∣
      (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ) := by
  apply (divides_coefficient_content_iff _ _ _).mpr
  constructor
  · unfold oddHankelIntegerA
    exact dvd_sub (cofactorContent_dvd_affine_determinant _ _)
      (cofactorContent_dvd_affine_determinant _ _)
  · exact cofactorContent_dvd_affine_determinant _ _

noncomputable def cofactorPrimitiveVector {n : ℕ}
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (j : Fin (n + 1)) : ℤ :=
  cofactorVector Z j / cofactorContent Z

theorem cofactorVector_lower_kernel {n : ℕ}
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (i : Fin (n + 1)) (hi : i ≠ 0) :
    ∑ j, (Z i j - Z 0 j) * cofactorVector Z j = 0 := by
  have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ => M i 0)
    (Matrix.mul_adjugate (cofactorDifferenceBase Z))
  simpa [Matrix.mul_apply, cofactorDifferenceBase, cofactorVector, hi] using h

theorem cofactor_affine_primitive_factorization {n : ℕ}
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (x : ℤ) :
    (arithmeticMatrixShift Z x).det = cofactorContent Z *
      (x * (∑ j, cofactorPrimitiveVector Z j) +
        ∑ j, Z 0 j * cofactorPrimitiveVector Z j) := by
  have hv (j : Fin (n + 1)) :
      cofactorVector Z j = cofactorContent Z * cofactorPrimitiveVector Z j := by
    unfold cofactorPrimitiveVector
    rw [mul_comm, Int.ediv_mul_cancel (cofactorContent_dvd Z j)]
  rw [affine_determinant_cofactor_expansion]
  simp_rw [hv]
  rw [← Finset.mul_sum]
  simp_rw [mul_left_comm (Z 0 _) (cofactorContent Z)]
  rw [← Finset.mul_sum]
  ring

theorem cofactor_full_content_factorization {n : ℕ}
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (Q : ℤ) :
    Int.gcd ((arithmeticMatrixShift Z Q).det - (arithmeticMatrixShift Z 0).det)
      (arithmeticMatrixShift Z 0).det =
      (cofactorContent Z).natAbs *
        Int.gcd (Q * (∑ j, cofactorPrimitiveVector Z j))
          (∑ j, Z 0 j * cofactorPrimitiveVector Z j) := by
  apply framed_comparison_content _ _ _ _ _ (LinearEquiv.refl ℤ (ℤ × ℤ))
  intro z
  change ((arithmeticMatrixShift Z Q).det - (arithmeticMatrixShift Z 0).det) * z.1 +
      (arithmeticMatrixShift Z 0).det * z.2 =
    cofactorContent Z *
      ((Q * (∑ j, cofactorPrimitiveVector Z j)) * z.1 +
        (∑ j, Z 0 j * cofactorPrimitiveVector Z j) * z.2)
  rw [cofactor_affine_primitive_factorization Z Q,
    cofactor_affine_primitive_factorization Z 0]
  ring

end OddZeta
