import OddZeta.AperyFive

namespace OddZeta

def constantMatrixShift {R : Type*} [CommRing R] {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (x : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j => x + H i j

theorem det_constantMatrixShift_affine {R : Type*} [CommRing R] {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (x : R) :
    (constantMatrixShift H x).det =
      ((constantMatrixShift H 1).det - (constantMatrixShift H 0).det) * x +
        (constantMatrixShift H 0).det := by
  classical
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    fun i j => if i = 0 then H 0 j else H i j - H 0 j
  have hd (y : R) : (Matrix.updateRow B 0 (fun j => y + H 0 j)).det =
      (constantMatrixShift H y).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 0 then 0 else -1) 0 (by simp)
    intro i j
    by_cases hi : i = 0
    · subst i
      simp [Matrix.updateRow, constantMatrixShift]
      rw [Function.update_self]
    · simp [Matrix.updateRow, constantMatrixShift, B, hi]
      ring
  have hf (y : R) : (constantMatrixShift H y).det =
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

def harmonicHankelBase (n shift : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i j => -harmonicFive (shift + i.val + j.val)

noncomputable def harmonicHankelA (n shift : ℕ) : ℚ :=
  (constantMatrixShift (harmonicHankelBase n shift) 1).det -
    (constantMatrixShift (harmonicHankelBase n shift) 0).det

noncomputable def harmonicHankelB (n shift : ℕ) : ℚ :=
  (constantMatrixShift (harmonicHankelBase n shift) 0).det

theorem harmonicHankel_affine (n shift : ℕ) (x : ℚ) :
    (constantMatrixShift (harmonicHankelBase n shift) x).det =
      harmonicHankelA n shift * x + harmonicHankelB n shift := by
  exact det_constantMatrixShift_affine (harmonicHankelBase n shift) x

theorem harmonicHankel_real_affine (n shift : ℕ) (x : ℝ) :
    Matrix.det (fun i j : Fin (n + 1) => x -
      (harmonicFive (shift + i.val + j.val) : ℝ)) =
      (harmonicHankelA n shift : ℝ) * x + (harmonicHankelB n shift : ℝ) := by
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => -(harmonicFive (shift + i.val + j.val) : ℝ)
  have hc (y : ℚ) :
      (((constantMatrixShift (harmonicHankelBase n shift) y).det : ℚ) : ℝ) =
        (constantMatrixShift H (y : ℝ)).det := by
    change (Rat.castHom ℝ) ((constantMatrixShift (harmonicHankelBase n shift) y).det) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [constantMatrixShift, harmonicHankelBase, H]
  have h := det_constantMatrixShift_affine H x
  have hc1 := hc 1
  have hc0 := hc 0
  norm_num at hc1 hc0
  rw [← hc1, ← hc0] at h
  have hm : (fun i j : Fin (n + 1) => x -
      (harmonicFive (shift + i.val + j.val) : ℝ)) = constantMatrixShift H x := by
    funext i j
    simp [constantMatrixShift, H]
    ring
  rw [hm]
  unfold harmonicHankelA harmonicHankelB
  rw [Rat.cast_sub]
  exact h

end OddZeta
