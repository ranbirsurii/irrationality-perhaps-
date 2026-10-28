import OddZeta.BinaryGaussMinimum

namespace OddZeta

def dualGramFirst (A B C ya yb : ℝ) : ℝ :=
  C * ya ^ 2 - 2 * B * ya * yb + A * yb ^ 2

def dualGramCross (A B C ya yb za zb : ℝ) : ℝ :=
  C * ya * za - B * (ya * zb + yb * za) + A * yb * zb

def dualGramSecond (A B C za zb : ℝ) : ℝ :=
  C * za ^ 2 - 2 * B * za * zb + A * zb ^ 2

theorem dual_gram_determinant_identity (A B C ya yb za zb : ℝ) :
    dualGramFirst A B C ya yb * dualGramSecond A B C za zb -
        dualGramCross A B C ya yb za zb ^ 2 =
      (ya * zb - yb * za) ^ 2 * (A * C - B ^ 2) := by
  unfold dualGramFirst dualGramSecond dualGramCross
  ring

theorem dual_gram_pullback_identity (A B C ya yb za zb p q : ℝ) :
    binaryQuadratic (dualGramFirst A B C ya yb)
      (dualGramCross A B C ya yb za zb) (dualGramSecond A B C za zb) p q =
      binaryQuadratic C (-B) A (p * ya + q * za) (p * yb + q * zb) := by
  unfold binaryQuadratic dualGramFirst dualGramCross dualGramSecond
  ring

theorem dual_gram_primal_adjugate_identity (A B C ya yb za zb : ℝ) :
    binaryQuadratic A B C zb (-za) = dualGramSecond A B C za zb ∧
      (A * zb * (-yb) + B * (zb * ya + (-za) * (-yb)) + C * (-za) * ya) =
        -dualGramCross A B C ya yb za zb ∧
      binaryQuadratic A B C (-yb) ya = dualGramFirst A B C ya yb := by
  unfold binaryQuadratic dualGramFirst dualGramCross dualGramSecond
  constructor
  · ring
  constructor <;> ring

theorem binary_adjugate_quarter_turn (A B C x y : ℝ) :
    binaryQuadratic C (-B) A x y = binaryQuadratic A B C (-y) x := by
  unfold binaryQuadratic
  ring

theorem binary_quadratic_positive (A B C x y : ℝ)
    (hA : 0 < A) (hdet : 0 < A * C - B ^ 2)
    (hnonzero : x ≠ 0 ∨ y ≠ 0) : 0 < binaryQuadratic A B C x y := by
  have hidentity : A * binaryQuadratic A B C x y =
      (A * x + B * y) ^ 2 + (A * C - B ^ 2) * y ^ 2 := by
    unfold binaryQuadratic
    ring
  by_cases hy : y = 0
  · have hx : x ≠ 0 := hnonzero.resolve_right (not_not.mpr hy)
    simpa [binaryQuadratic, hy] using mul_pos hA (sq_pos_of_ne_zero hx)
  · have hp := mul_pos hdet (sq_pos_of_ne_zero hy)
    have hs := sq_nonneg (A * x + B * y)
    have hproduct : 0 < A * binaryQuadratic A B C x y := by linarith
    exact (mul_pos_iff_of_pos_left hA).mp hproduct

theorem coefficient_row_pair_nonzero (ya yb za zb p q : ℝ)
    (hdet : ya * zb - yb * za ≠ 0) (hnonzero : p ≠ 0 ∨ q ≠ 0) :
    p * ya + q * za ≠ 0 ∨ p * yb + q * zb ≠ 0 := by
  by_cases hfirst : p * ya + q * za = 0
  · right
    intro hsecond
    have hp : (ya * zb - yb * za) * p = 0 := by
      calc
        _ = zb * (p * ya + q * za) - za * (p * yb + q * zb) := by ring
        _ = 0 := by rw [hfirst, hsecond]; ring
    have hq : (ya * zb - yb * za) * q = 0 := by
      calc
        _ = ya * (p * yb + q * zb) - yb * (p * ya + q * za) := by ring
        _ = 0 := by rw [hfirst, hsecond]; ring
    have hpzero := (mul_eq_zero.mp hp).resolve_left hdet
    have hqzero := (mul_eq_zero.mp hq).resolve_left hdet
    exact hnonzero.elim (fun h => h hpzero) (fun h => h hqzero)
  · exact Or.inl hfirst

theorem dual_gram_quadratic_positive (A B C ya yb za zb p q : ℝ)
    (hC : 0 < C) (hgram : 0 < A * C - B ^ 2)
    (hdet : ya * zb - yb * za ≠ 0) (hnonzero : p ≠ 0 ∨ q ≠ 0) :
    0 < binaryQuadratic (dualGramFirst A B C ya yb)
      (dualGramCross A B C ya yb za zb) (dualGramSecond A B C za zb) p q := by
  rw [dual_gram_pullback_identity]
  apply binary_quadratic_positive C (-B) A _ _ hC
  · nlinarith
  · exact coefficient_row_pair_nonzero ya yb za zb p q hdet hnonzero

end OddZeta
