import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp

namespace OddZeta

theorem rational_centering_den_divisibilities (x c : ℚ) :
    (x - c).den ∣ x.den * c.den ∧ x.den ∣ (x - c).den * c.den := by
  constructor
  · exact Rat.sub_den_dvd x c
  · have h := Rat.add_den_dvd (x - c) c
    simpa only [sub_add_cancel] using h

theorem rational_centering_den_bounds (x c : ℚ) :
    (x - c).den ≤ x.den * c.den ∧ x.den ≤ (x - c).den * c.den := by
  have h := rational_centering_den_divisibilities x c
  exact ⟨Nat.le_of_dvd (Nat.mul_pos x.den_pos c.den_pos) h.1,
    Nat.le_of_dvd (Nat.mul_pos (x - c).den_pos c.den_pos) h.2⟩

theorem integer_centering_preserves_denominator (x : ℚ) (k : ℤ) :
    (x - k).den = x.den := Rat.sub_intCast_den x k

theorem rational_rescaling_preserves_primitive_height (A B c : ℚ) (hc : c ≠ 0) :
    ((c * B) / (c * A)).den = (B / A).den := by
  have h : (c * B) / (c * A) = B / A := by
    by_cases hA : A = 0
    · simp [hA]
    · field_simp
  exact congrArg Rat.den h

end OddZeta
