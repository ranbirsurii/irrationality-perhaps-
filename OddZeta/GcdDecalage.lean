import OddZeta.OddHankelArithmetic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace OddZeta

open CategoryTheory

def coefficientRow {R : Type*} [CommRing R] (U V : R) : (R × R) →ₗ[R] R where
  toFun z := U * z.1 + V * z.2
  map_add' z w := by simp; ring
  map_smul' c z := by simp; ring

theorem coefficientRow_image (U V z : ℤ) :
    (∃ x y : ℤ, U * x + V * y = z) ↔ (Int.gcd U V : ℤ) ∣ z := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left U V) x)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right U V) y)
  · rintro ⟨k, hk⟩
    refine ⟨Int.gcdA U V * k, Int.gcdB U V * k, ?_⟩
    rw [hk, Int.gcd_eq_gcd_ab]
    ring

theorem coefficientRow_range (U V : ℤ) :
    LinearMap.range (coefficientRow U V) =
      Ideal.span ({(Int.gcd U V : ℤ)} : Set ℤ) := by
  ext z
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨⟨x, y⟩, h⟩
    exact (coefficientRow_image U V z).mp ⟨x, y, h⟩
  · intro h
    obtain ⟨x, y, hxy⟩ := (coefficientRow_image U V z).mpr h
    exact ⟨(x, y), hxy⟩

theorem divides_coefficient_content_iff (d U V : ℤ) :
    d ∣ (Int.gcd U V : ℤ) ↔ d ∣ U ∧ d ∣ V := by
  constructor
  · intro h
    exact ⟨h.trans (Int.gcd_dvd_left U V), h.trans (Int.gcd_dvd_right U V)⟩
  · rintro ⟨hU, hV⟩
    rw [Int.gcd_eq_gcd_ab]
    exact dvd_add (dvd_mul_of_dvd_left hU _) (dvd_mul_of_dvd_left hV _)

def etaZeroLattice (U V d : ℤ) : Submodule ℤ (ℤ × ℤ) :=
  Submodule.comap (coefficientRow U V) (Ideal.span ({d} : Set ℤ))

theorem mem_etaZeroLattice (U V d : ℤ) (z : ℤ × ℤ) :
    z ∈ etaZeroLattice U V d ↔ d ∣ U * z.1 + V * z.2 := by
  simp [etaZeroLattice, coefficientRow, Ideal.mem_span_singleton]

theorem etaZeroLattice_eq_top_iff (U V d : ℤ) :
    etaZeroLattice U V d = ⊤ ↔ d ∣ U ∧ d ∣ V := by
  constructor
  · intro h
    have hmem (z : ℤ × ℤ) : d ∣ U * z.1 + V * z.2 := by
      apply (mem_etaZeroLattice U V d z).mp
      rw [h]
      trivial
    exact ⟨by simpa using hmem (1, 0), by simpa using hmem (0, 1)⟩
  · rintro ⟨hU, hV⟩
    apply Submodule.ext
    intro z
    simp only [Submodule.mem_top, iff_true]
    apply (mem_etaZeroLattice U V d z).mpr
    exact dvd_add (dvd_mul_of_dvd_left hU _) (dvd_mul_of_dvd_left hV _)

theorem coefficientRow_division_base_change {R : Type*} [CommRing R]
    (U V d : ℤ) (hU : d ∣ U) (hV : d ∣ V) (x y : R) :
    (U : R) * x + (V : R) * y =
      (d : R) * (((U / d : ℤ) : R) * x + ((V / d : ℤ) : R) * y) := by
  have ha := congrArg (fun z : ℤ => (z : R)) (Int.ediv_mul_cancel hU)
  have hb := congrArg (fun z : ℤ => (z : R)) (Int.ediv_mul_cancel hV)
  simp only [Int.cast_mul] at ha hb
  rw [← ha, ← hb]
  ring

theorem coefficientRow_range_base_change (R : Type*) [CommRing R] (U V : ℤ) :
    LinearMap.range (coefficientRow (U : R) (V : R)) =
      Ideal.span ({((Int.gcd U V : ℤ) : R)} : Set R) := by
  ext z
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨((U / (Int.gcd U V : ℤ) : ℤ) : R) * w.1 +
      ((V / (Int.gcd U V : ℤ) : ℤ) : R) * w.2, ?_⟩
    exact coefficientRow_division_base_change U V (Int.gcd U V : ℤ)
      (Int.gcd_dvd_left U V) (Int.gcd_dvd_right U V) w.1 w.2
  · rintro ⟨k, hk⟩
    have hb : ((Int.gcd U V : ℤ) : R) =
        (U : R) * (Int.gcdA U V : R) + (V : R) * (Int.gcdB U V : R) := by
      simpa only [Int.cast_add, Int.cast_mul] using
        congrArg (fun z : ℤ => (z : R)) (Int.gcd_eq_gcd_ab U V)
    refine ⟨((Int.gcdA U V : R) * k, (Int.gcdB U V : R) * k), ?_⟩
    change (U : R) * ((Int.gcdA U V : R) * k) +
      (V : R) * ((Int.gcdB U V : R) * k) = z
    rw [hk, hb]
    ring

theorem primitive_coefficient_bezout (U V : ℤ) (hg : Int.gcd U V ≠ 0) :
    Int.gcdA U V * (U / (Int.gcd U V : ℤ)) +
      Int.gcdB U V * (V / (Int.gcd U V : ℤ)) = 1 := by
  have hgZ : (Int.gcd U V : ℤ) ≠ 0 := by exact_mod_cast hg
  apply mul_left_cancel₀ hgZ
  have ha := Int.ediv_mul_cancel (Int.gcd_dvd_left U V)
  have hb := Int.ediv_mul_cancel (Int.gcd_dvd_right U V)
  calc
    (Int.gcd U V : ℤ) *
        (Int.gcdA U V * (U / (Int.gcd U V : ℤ)) +
          Int.gcdB U V * (V / (Int.gcd U V : ℤ))) =
        (U / (Int.gcd U V : ℤ) * (Int.gcd U V : ℤ)) * Int.gcdA U V +
          (V / (Int.gcd U V : ℤ) * (Int.gcd U V : ℤ)) * Int.gcdB U V := by ring
    _ = U * Int.gcdA U V + V * Int.gcdB U V := by rw [ha, hb]
    _ = (Int.gcd U V : ℤ) := (Int.gcd_eq_gcd_ab U V).symm
    _ = (Int.gcd U V : ℤ) * 1 := by ring

def coefficientSmithMatrix (U V : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![Int.gcdA U V, -(V / (Int.gcd U V : ℤ));
     Int.gcdB U V, U / (Int.gcd U V : ℤ)]

theorem coefficientSmithMatrix_det (U V : ℤ) (hg : Int.gcd U V ≠ 0) :
    (coefficientSmithMatrix U V).det = 1 := by
  rw [Matrix.det_fin_two]
  have h := primitive_coefficient_bezout U V hg
  simpa [coefficientSmithMatrix, mul_comm, sub_eq_add_neg] using h

theorem coefficientSmith_boundary (U V x y : ℤ) :
    U * (Int.gcdA U V * x - (V / (Int.gcd U V : ℤ)) * y) +
      V * (Int.gcdB U V * x + (U / (Int.gcd U V : ℤ)) * y) =
        (Int.gcd U V : ℤ) * x := by
  have ha := Int.ediv_mul_cancel (Int.gcd_dvd_left U V)
  have hb := Int.ediv_mul_cancel (Int.gcd_dvd_right U V)
  have hz : U * (V / (Int.gcd U V : ℤ)) =
      V * (U / (Int.gcd U V : ℤ)) := by
    calc
      _ = ((U / (Int.gcd U V : ℤ)) * (Int.gcd U V : ℤ)) *
          (V / (Int.gcd U V : ℤ)) := by rw [ha]
      _ = ((V / (Int.gcd U V : ℤ)) * (Int.gcd U V : ℤ)) *
          (U / (Int.gcd U V : ℤ)) := by ring
      _ = _ := by rw [hb]
  calc
    _ = (U * Int.gcdA U V + V * Int.gcdB U V) * x +
        (V * (U / (Int.gcd U V : ℤ)) - U * (V / (Int.gcd U V : ℤ))) * y := by ring
    _ = _ := by rw [← Int.gcd_eq_gcd_ab, hz]; ring

theorem content_prime_power_iff (U V : ℤ) (p k : ℕ) :
    ((p ^ k : ℕ) : ℤ) ∣ (Int.gcd U V : ℤ) ↔
      ((p ^ k : ℕ) : ℤ) ∣ U ∧ ((p ^ k : ℕ) : ℤ) ∣ V :=
  divides_coefficient_content_iff _ U V

theorem content_tropical_weight (U V : ℤ) (hU : U ≠ 0) (hV : V ≠ 0) (p : ℕ) :
    (Int.gcd U V).factorization p =
      min (U.natAbs.factorization p) (V.natAbs.factorization p) := by
  change (U.natAbs.gcd V.natAbs).factorization p = _
  have h := congrArg (fun f : ℕ →₀ ℕ => f p)
    (Nat.factorization_gcd (Int.natAbs_ne_zero.mpr hU) (Int.natAbs_ne_zero.mpr hV))
  simpa using h

def coefficientObjects (R : Type*) [CommRing R] : ℕ → ModuleCat R
  | 0 => ModuleCat.of R (R × R)
  | 1 => ModuleCat.of R R
  | _ + 2 => ModuleCat.of R PUnit

def coefficientDifferential (R : Type*) [CommRing R] (U V : ℤ) :
    ∀ n, coefficientObjects R n ⟶ coefficientObjects R (n + 1)
  | 0 => ModuleCat.ofHom (coefficientRow (U : R) (V : R))
  | _ + 1 => 0

def coefficientComplex (R : Type*) [CommRing R] (U V : ℤ) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (coefficientObjects R) (coefficientDifferential R U V) (by
    intro n
    cases n <;> simp only [coefficientDifferential]
    · ext z
      rfl
    · ext z
      rfl)

theorem coefficientComplex_first_differential (R : Type*) [CommRing R] (U V : ℤ) :
    (coefficientComplex R U V).d 0 1 =
      ModuleCat.ofHom (coefficientRow (U : R) (V : R)) := by
  change CochainComplex.of.d (coefficientObjects R) (coefficientDifferential R U V) 0 (0 + 1) = _
  rw [CochainComplex.of_d]
  rfl

def coefficientRescaling (R : Type*) [CommRing R] (d : ℤ) :
    ∀ n, coefficientObjects R n ⟶ coefficientObjects R n
  | 0 => CategoryTheory.CategoryStruct.id _
  | 1 => ModuleCat.ofHom ((d : R) • (LinearMap.id : R →ₗ[R] R))
  | _ + 2 => 0

def coefficientDivisionComparison (R : Type*) [CommRing R] (U V d : ℤ)
    (hU : d ∣ U) (hV : d ∣ V) :
    coefficientComplex R (U / d) (V / d) ⟶ coefficientComplex R U V :=
  CochainComplex.ofHom (coefficientRescaling R d) (by
    intro n
    change coefficientRescaling R d n ≫
        CochainComplex.of.d (coefficientObjects R) (coefficientDifferential R U V) n (n + 1) =
      CochainComplex.of.d (coefficientObjects R)
        (coefficientDifferential R (U / d) (V / d)) n (n + 1) ≫
          coefficientRescaling R d (n + 1)
    rw [CochainComplex.of_d, CochainComplex.of_d]
    cases n with
    | zero =>
      ext z
      change (U : R) * z.1 + (V : R) * z.2 =
        (d : R) * (((U / d : ℤ) : R) * z.1 + ((V / d : ℤ) : R) * z.2)
      exact coefficientRow_division_base_change U V d hU hV z.1 z.2
    | succ n =>
      cases n <;> (ext; rfl))

noncomputable def oddHankelCoefficientComplex (s n a : ℕ) : CochainComplex (ModuleCat ℤ) ℕ :=
  coefficientComplex ℤ (oddHankelIntegerA s n a) (oddHankelIntegerB s n a)

noncomputable def oddHankelPadicComplex (s n a p : ℕ) [Fact p.Prime] :
    CochainComplex (ModuleCat (PadicInt p)) ℕ :=
  coefficientComplex (PadicInt p) (oddHankelIntegerA s n a) (oddHankelIntegerB s n a)

noncomputable def oddHankelPadicPrimitiveComparison (s n a p : ℕ) [Fact p.Prime] :
    coefficientComplex (PadicInt p)
      (oddHankelIntegerA s n a /
        (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ))
      (oddHankelIntegerB s n a /
        (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ)) ⟶
      oddHankelPadicComplex s n a p :=
  coefficientDivisionComparison (PadicInt p) _ _ _
    (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)

theorem oddHankel_etaZero_full (s n a : ℕ) :
    etaZeroLattice (oddHankelIntegerA s n a) (oddHankelIntegerB s n a)
      (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ) = ⊤ := by
  apply (etaZeroLattice_eq_top_iff _ _ _).mpr
  exact ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩

theorem oddHankel_prime_decalage_eligibility (s n a p k : ℕ) :
    etaZeroLattice (oddHankelIntegerA s n a) (oddHankelIntegerB s n a)
      ((p ^ k : ℕ) : ℤ) = ⊤ ↔
      ((p ^ k : ℕ) : ℤ) ∣
        (Int.gcd (oddHankelIntegerA s n a) (oddHankelIntegerB s n a) : ℤ) := by
  rw [etaZeroLattice_eq_top_iff, divides_coefficient_content_iff]

end OddZeta
