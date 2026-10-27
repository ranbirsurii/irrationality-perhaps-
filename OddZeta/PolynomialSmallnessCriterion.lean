import OddZeta.OddHankelArithmetic
import Mathlib.RingTheory.Polynomial.ScaleRoots

namespace OddZeta

theorem integer_polynomial_rational_gap (P : Polynomial ℤ) (p d : ℤ) (hd : d ≠ 0)
    (hne : P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / (d : ℝ)) ≠ 0) :
    1 ≤ |(d : ℝ)| ^ P.natDegree *
      |P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / (d : ℝ))| := by
  let z : ℤ := (P.scaleRoots d).eval p
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have harg : (d : ℝ) * ((p : ℝ) / (d : ℝ)) = (p : ℝ) := by field_simp
  have hz : (z : ℝ) = (d : ℝ) ^ P.natDegree *
      P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / (d : ℝ)) := by
    have h := Polynomial.scaleRoots_eval₂_mul (p := P)
      (Int.castRingHom ℝ) ((p : ℝ) / (d : ℝ)) d
    change (P.scaleRoots d).eval₂ (Int.castRingHom ℝ)
      ((d : ℝ) * ((p : ℝ) / (d : ℝ))) = _ at h
    rw [harg] at h
    calc
      (z : ℝ) = (P.scaleRoots d).eval₂ (Int.castRingHom ℝ) (p : ℝ) :=
        (Polynomial.eval₂_at_apply (p := P.scaleRoots d) (Int.castRingHom ℝ) p).symm
      _ = _ := h
  have hzR : (z : ℝ) ≠ 0 := by
    rw [hz]
    exact mul_ne_zero (pow_ne_zero _ hdR) hne
  have hzZ : z ≠ 0 := by exact_mod_cast hzR
  have hb : (1 : ℤ) ≤ |z| := by have h := abs_pos.mpr hzZ; omega
  have hbR : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast hb
  simpa only [hz, abs_mul, abs_pow] using hbR

theorem arithmeticIrrationalOfPolynomialForms (α : ℝ)
    (hsmall : ∀ q : ℕ, 0 < q → ∃ P : Polynomial ℤ,
      P.eval₂ (Int.castRingHom ℝ) α ≠ 0 ∧
      (q : ℝ) ^ P.natDegree * |P.eval₂ (Int.castRingHom ℝ) α| < 1) :
    Irrational α := by
  rw [irrational_iff_ne_rational]
  intro p d hd hα
  obtain ⟨P, hne, hsmallP⟩ := hsmall d.natAbs (Int.natAbs_pos.mpr hd)
  have hgap := integer_polynomial_rational_gap P p d hd (by simpa only [← hα] using hne)
  rw [← hα] at hgap
  have habs : |(d : ℝ)| = (d.natAbs : ℝ) := by
    rw [← Int.cast_abs]
    exact congrArg (fun x : ℤ => (x : ℝ)) (Int.natCast_natAbs d).symm
  rw [habs] at hgap
  linarith

end OddZeta
