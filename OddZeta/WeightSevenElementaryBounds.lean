import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OddZeta

def weightSevenStationary (y : ℝ) : ℝ := 5*y^4-2*y^3-13*y^2-7*y-1

theorem weight_seven_stationary_factor (x : ℝ) :
    (x-1)*(x+1)^8-x^8*(x+2) = weightSevenStationary (x*(x+1)) := by
  unfold weightSevenStationary
  ring

theorem weight_seven_stationary_shift (z : ℝ) :
    weightSevenStationary (2+z) = 5*z^4+38*z^3+95*z^2+77*z-3 := by
  unfold weightSevenStationary
  ring

theorem weight_seven_stationary_upper_endpoint :
    0 < weightSevenStationary (((25309:ℝ)/25000)*((25309:ℝ)/25000+1)) := by
  norm_num [weightSevenStationary]

theorem weight_seven_saddle_base_bound :
    2397 * (((25309:ℝ)/25000)+2)^2 * (((25309:ℝ)/25000)-1) <
      (((25309:ℝ)/25000)+1)^8 := by
  norm_num

theorem weight_seven_moment_cutoff (n : ℝ) (hn : 6 ≤ n) :
    2*(n-3) ≤ 3*n ∧
      2*(n-3)^2+7*n*(n+1) ≤ 3*n*(7*(n+1)-2*(n-3)-8) := by
  constructor
  · linarith
  · nlinarith [sq_nonneg n]

end OddZeta
