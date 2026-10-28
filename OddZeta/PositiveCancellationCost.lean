import OddZeta.KernelProjectorContent
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OddZeta

theorem balanced_positive_kernel_mass_lower
    (t a b c : ℤ) (ht : 2 ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hne : 0 < a + b + c)
    (hker : t * a - (t - 1) * b + t * c = 0) :
    2 * t - 1 ≤ a + b + c := by
  have hs : 0 < a + c := by
    by_contra hn
    have hz : a + c = 0 := by omega
    have hprod : b ≤ (t - 1) * b := by
      simpa using mul_le_mul_of_nonneg_right (show 1 ≤ t - 1 by omega) hb
    nlinarith
  have hdiff : a + c < b := by
    by_contra hn
    have hle : b ≤ a + c := by omega
    have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ t - 1 by omega)
    nlinarith
  have hk : 1 ≤ b - a - c := by omega
  have heq : a + b + c = (2 * t - 1) * (b - a - c) := by
    nlinarith
  rw [heq]
  simpa using mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * t - 1 by omega)

theorem balanced_positive_kernel_mass_attained (t : ℤ) (ht : 2 ≤ t) :
    0 ≤ t - 1 ∧ 0 ≤ t ∧
      t * (t - 1) - (t - 1) * t + t * 0 = 0 ∧
      (t - 1) + t + 0 = 2 * t - 1 := by
  constructor
  · omega
  constructor
  · omega
  constructor <;> ring

theorem balanced_positive_row_ratio (t : ℝ) (ht : 2 ≤ t) :
    2 * t / (t - 1) ≤ 4 := by
  rw [div_le_iff₀ (by linarith : 0 < t - 1)]
  linarith

theorem balanced_kernel_target_content_is_unit (t g : ℤ)
    (hdiv : ∀ a b c : ℤ, t * a - (t - 1) * b + t * c = 0 →
      g ∣ a ∧ g ∣ c) : g ∣ 1 := by
  exact (hdiv 1 0 (-1) (by ring)).1

end OddZeta
