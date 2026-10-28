import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OddZeta

def coefficientPairMap (a b c d : ℚ) (x : ℚ × ℚ) : ℚ × ℚ :=
  (a * x.1 + b * x.2, c * x.1 + d * x.2)

def coefficientPairInverse (a b c d : ℚ) (y : ℚ × ℚ) : ℚ × ℚ :=
  ((d * y.1 - b * y.2) / (a * d - b * c),
   (a * y.2 - c * y.1) / (a * d - b * c))

theorem coefficientPairMap_inverse (a b c d : ℚ) (y : ℚ × ℚ)
    (hdet : a * d - b * c ≠ 0) :
    coefficientPairMap a b c d (coefficientPairInverse a b c d y) = y := by
  apply Prod.ext <;> dsimp [coefficientPairMap, coefficientPairInverse]
  · calc
      _ = ((a * d - b * c) * y.1) / (a * d - b * c) := by ring
      _ = y.1 := mul_div_cancel_left₀ _ hdet
  · calc
      _ = ((a * d - b * c) * y.2) / (a * d - b * c) := by ring
      _ = y.2 := mul_div_cancel_left₀ _ hdet

theorem coefficientPairInverse_map (a b c d : ℚ) (x : ℚ × ℚ)
    (hdet : a * d - b * c ≠ 0) :
    coefficientPairInverse a b c d (coefficientPairMap a b c d x) = x := by
  apply Prod.ext <;> dsimp [coefficientPairMap, coefficientPairInverse]
  · calc
      _ = ((a * d - b * c) * x.1) / (a * d - b * c) := by ring
      _ = x.1 := mul_div_cancel_left₀ _ hdet
  · calc
      _ = ((a * d - b * c) * x.2) / (a * d - b * c) := by ring
      _ = x.2 := mul_div_cancel_left₀ _ hdet

def hasIntegralCoefficientImage (a b c d : ℚ) (x : ℚ × ℚ) : Prop :=
  ∃ u v : ℤ, coefficientPairMap a b c d x = ((u : ℚ), (v : ℚ))

theorem integral_image_iff_inverse_integer_pair (a b c d : ℚ) (x : ℚ × ℚ)
    (hdet : a * d - b * c ≠ 0) :
    hasIntegralCoefficientImage a b c d x ↔
      ∃ u v : ℤ, x = coefficientPairInverse a b c d ((u : ℚ), (v : ℚ)) := by
  constructor
  · rintro ⟨u, v, h⟩
    refine ⟨u, v, ?_⟩
    calc
      x = coefficientPairInverse a b c d (coefficientPairMap a b c d x) :=
        (coefficientPairInverse_map a b c d x hdet).symm
      _ = _ := congrArg (coefficientPairInverse a b c d) h
  · rintro ⟨u, v, rfl⟩
    exact ⟨u, v, coefficientPairMap_inverse a b c d ((u : ℚ), (v : ℚ)) hdet⟩

theorem integer_adjugate_lift (a b c d u v : ℤ) :
    a * (d * u - b * v) + b * (a * v - c * u) = (a * d - b * c) * u ∧
      c * (d * u - b * v) + d * (a * v - c * u) = (a * d - b * c) * v := by
  constructor <;> ring

theorem square_adjugate_lift (a b c d u v : ℤ) :
    a * ((a * d - b * c) * (d * u - b * v)) +
        b * ((a * d - b * c) * (a * v - c * u)) = (a * d - b * c) ^ 2 * u ∧
      c * ((a * d - b * c) * (d * u - b * v)) +
        d * ((a * d - b * c) * (a * v - c * u)) = (a * d - b * c) ^ 2 * v := by
  constructor <;> ring

theorem square_scaled_primitive_content (g u v : ℤ) (hprimitive : Int.gcd u v = 1) :
    (Int.gcd (g ^ 2 * u) (g ^ 2 * v) : ℤ) = g ^ 2 := by
  rw [Int.gcd_mul_left, hprimitive, mul_one]
  simp only [Int.natCast_natAbs, abs_of_nonneg (sq_nonneg g)]

theorem square_adjugate_normalization (a b c d : ℚ) (y : ℚ × ℚ)
    (hdet : a * d - b * c ≠ 0) :
    (((a * d - b * c) * (d * y.1 - b * y.2)) / (a * d - b * c) ^ 2,
     ((a * d - b * c) * (a * y.2 - c * y.1)) / (a * d - b * c) ^ 2) =
      coefficientPairInverse a b c d y := by
  apply Prod.ext <;> dsimp [coefficientPairInverse]
  · field_simp
  · field_simp

theorem divided_kernel_coordinates_have_integral_image
    (a b c d x y h : ℤ)
    (hfirst : h ∣ a * x + b * y) (hsecond : h ∣ c * x + d * y)
    (hh : (h : ℚ) ≠ 0) :
    hasIntegralCoefficientImage a b c d ((x : ℚ) / h, (y : ℚ) / h) := by
  refine ⟨(a * x + b * y) / h, (c * x + d * y) / h, ?_⟩
  apply Prod.ext <;> dsimp [coefficientPairMap]
  · rw [Int.cast_div hfirst hh]
    push_cast
    ring
  · rw [Int.cast_div hsecond hh]
    push_cast
    ring

end OddZeta
