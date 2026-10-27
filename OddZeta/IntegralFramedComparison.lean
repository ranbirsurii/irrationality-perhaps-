import OddZeta.GcdDecalage
import Mathlib.LinearAlgebra.Quotient.Basic

namespace OddZeta

abbrev coefficientCokernel (R : Type*) [CommRing R] (U V : ℤ) :=
  R ⧸ LinearMap.range (coefficientRow (U : R) (V : R))

noncomputable def coefficientCokernelContentEquiv (R : Type*) [CommRing R] (U V : ℤ) :
    coefficientCokernel R U V ≃ₗ[R]
      R ⧸ Ideal.span ({((Int.gcd U V : ℤ) : R)} : Set R) :=
  Submodule.quotEquivOfEq _ _ (coefficientRow_range_base_change R U V)

theorem primitive_coefficientRow_surjective (R : Type*) [CommRing R]
    (U V : ℤ) (hg : Int.gcd U V ≠ 0) :
    Function.Surjective (coefficientRow
      ((U / (Int.gcd U V : ℤ) : ℤ) : R)
      ((V / (Int.gcd U V : ℤ) : ℤ) : R)) := by
  intro z
  refine ⟨((Int.gcdA U V : R) * z, (Int.gcdB U V : R) * z), ?_⟩
  have hb := congrArg (fun k : ℤ => (k : R)) (primitive_coefficient_bezout U V hg)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_one] at hb
  change ((U / (Int.gcd U V : ℤ) : ℤ) : R) * ((Int.gcdA U V : R) * z) +
    ((V / (Int.gcd U V : ℤ) : ℤ) : R) * ((Int.gcdB U V : R) * z) = z
  calc
    _ = ((Int.gcdA U V : R) * ((U / (Int.gcd U V : ℤ) : ℤ) : R) +
      (Int.gcdB U V : R) * ((V / (Int.gcd U V : ℤ) : ℤ) : R)) * z := by ring
    _ = z := by rw [hb, one_mul]

theorem primitive_coefficientRow_range (R : Type*) [CommRing R]
    (U V : ℤ) (hg : Int.gcd U V ≠ 0) :
    LinearMap.range (coefficientRow
      ((U / (Int.gcd U V : ℤ) : ℤ) : R)
      ((V / (Int.gcd U V : ℤ) : ℤ) : R)) = ⊤ :=
  LinearMap.range_eq_top.mpr (primitive_coefficientRow_surjective R U V hg)

theorem framed_comparison_content_divisibility
    (U V A B d : ℤ) (e : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ))
    (h : ∀ z, coefficientRow U V (e z) = d * coefficientRow A B z)
    (c : ℤ) :
    c ∣ (Int.gcd U V : ℤ) ↔ c ∣ d * (Int.gcd A B : ℤ) := by
  have hsource : coefficientRow A B (Int.gcdA A B, Int.gcdB A B) =
      (Int.gcd A B : ℤ) := (Int.gcd_eq_gcd_ab A B).symm
  constructor
  · intro hc
    have hz : c ∣ coefficientRow U V (e (Int.gcdA A B, Int.gcdB A B)) := by
      exact hc.trans ((coefficientRow_image U V _).mp
        ⟨(e (Int.gcdA A B, Int.gcdB A B)).1,
          (e (Int.gcdA A B, Int.gcdB A B)).2, rfl⟩)
    rwa [h, hsource] at hz
  · intro hc
    have hz (w : ℤ × ℤ) : c ∣ coefficientRow U V w := by
      obtain ⟨z, rfl⟩ := e.surjective w
      rw [h]
      obtain ⟨k, hk⟩ := (coefficientRow_image A B _).mp ⟨z.1, z.2, rfl⟩
      exact hc.trans ⟨k, by change d * (A * z.1 + B * z.2) = _; rw [hk]; ring⟩
    apply (divides_coefficient_content_iff c U V).mpr
    exact ⟨by simpa [coefficientRow] using hz (1, 0),
      by simpa [coefficientRow] using hz (0, 1)⟩

theorem framed_comparison_content
    (U V A B d : ℤ) (e : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ))
    (h : ∀ z, coefficientRow U V (e z) = d * coefficientRow A B z) :
    Int.gcd U V = d.natAbs * Int.gcd A B := by
  have hforward := (framed_comparison_content_divisibility U V A B d e h
    (Int.gcd U V : ℤ)).mp dvd_rfl
  have hbackward := (framed_comparison_content_divisibility U V A B d e h
    (d * (Int.gcd A B : ℤ))).mpr dvd_rfl
  have hf := Int.natAbs_dvd_natAbs.mpr hforward
  have hb := Int.natAbs_dvd_natAbs.mpr hbackward
  simpa only [Int.natAbs_natCast, Int.natAbs_mul] using Nat.dvd_antisymm hf hb

theorem rational_coefficient_range_loses_content (m : ℕ) :
    LinearMap.range (coefficientRow (m : ℚ) 0) = ⊤ ↔ m ≠ 0 := by
  constructor
  · intro h hm
    subst m
    simp only [Nat.cast_zero] at h
    have hm : (1 : ℚ) ∈ LinearMap.range (coefficientRow (0 : ℚ) 0) := by
      rw [h]
      trivial
    obtain ⟨z, hz⟩ := hm
    simp [coefficientRow] at hz
  · intro hm
    apply LinearMap.range_eq_top.mpr
    intro z
    refine ⟨(z / (m : ℚ), 0), ?_⟩
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    change (m : ℚ) * (z / (m : ℚ)) + 0 * 0 = z
    field_simp
    ring

end OddZeta
