import OddZeta.PoisedKernelPositivity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OddZeta

def normalizedOddKernel (r n m : ℕ) (t : ℚ) : ℚ :=
  (n.factorial : ℚ)^(2*r+1)/(m.factorial : ℚ)^2 * poisedRationalKernel r n m t

theorem poised_kernel_weight_shift (r n m : ℕ) (t : ℚ) :
    poisedRationalKernel (r+1) n m t =
      poisedRationalKernel r n m t / (∏ j ∈ Finset.range (n+1), (t+(j:ℚ)))^2 := by
  unfold poisedRationalKernel
  have h : 2*(r+1)+1=(2*r+1)+2 := by omega
  simp_rw [h, pow_add, Finset.prod_mul_distrib, Finset.prod_pow]
  rw [div_div]

theorem normalized_kernel_weight_shift (r n m : ℕ) (t : ℚ) :
    normalizedOddKernel (r+1) n m t = normalizedOddKernel r n m t *
      ((n.factorial : ℚ)/(∏ j ∈ Finset.range (n+1), (t+(j:ℚ))))^2 := by
  unfold normalizedOddKernel
  rw [poised_kernel_weight_shift]
  have h : 2*(r+1)+1=(2*r+1)+2 := by omega
  rw [h,pow_add,div_pow]
  ring

theorem poised_kernel_length_shift (r n m k : ℕ) (t : ℚ) :
    poisedRationalKernel r n (m+k) t = poisedRationalKernel r n m t *
      ∏ v ∈ Finset.range k,
        (t-((m+v+1:ℕ):ℚ))*(t+n+((m+v+1:ℕ):ℚ)) := by
  unfold poisedRationalKernel
  rw [Finset.prod_range_add]
  ring

theorem normalized_kernel_length_shift (r n m k : ℕ) (t : ℚ) :
    normalizedOddKernel r n (m+k) t = normalizedOddKernel r n m t *
      ((m.factorial:ℚ)/((m+k).factorial:ℚ))^2 *
      ∏ v ∈ Finset.range k,
        (t-((m+v+1:ℕ):ℚ))*(t+n+((m+v+1:ℕ):ℚ)) := by
  have hm : (m.factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hk : ((m+k).factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m+k)
  unfold normalizedOddKernel
  rw [poised_kernel_length_shift,div_pow]
  field_simp

noncomputable def oddKernelEntropy (x : ℝ) : ℝ :=
  (x+1)*Real.log (x+1)-x*Real.log x

noncomputable def oddKernelPhase (s x : ℝ) : ℝ :=
  -(s+1)*oddKernelEntropy x+(x+2)*Real.log (x+2)-(x-1)*Real.log (x-1)

theorem odd_kernel_phase_weight_shift (s x : ℝ) :
    oddKernelPhase (s+2) x=oddKernelPhase s x-2*oddKernelEntropy x := by
  unfold oddKernelPhase
  ring

theorem odd_kernel_entropy_derivative (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt oddKernelEntropy (Real.log (x+1)-Real.log x) x := by
  have hp := (Real.hasDerivAt_mul_log (by linarith : x+1 ≠ 0)).comp x
    ((hasDerivAt_id x).add_const 1)
  have hm := Real.hasDerivAt_mul_log (by linarith : x ≠ 0)
  convert hp.sub hm using 1 <;> first | rfl | ring

theorem odd_kernel_entropy_lower (x : ℝ) (hx : 1 ≤ x) :
    2*Real.log 2 ≤ oddKernelEntropy x := by
  have hcont : Continuous oddKernelEntropy := by
    unfold oddKernelEntropy
    exact (Real.continuous_mul_log.comp (continuous_id.add_const 1)).sub
      Real.continuous_mul_log
  have hmono : MonotoneOn oddKernelEntropy (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) hcont.continuousOn
    · intro y hy
      have hy' : 1 ≤ y := Set.mem_Ici.mp (interior_subset hy)
      exact (odd_kernel_entropy_derivative y hy').differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : 1 ≤ y := Set.mem_Ici.mp (interior_subset hy)
      rw [(odd_kernel_entropy_derivative y hy').deriv]
      exact sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have h := hmono (show (1:ℝ)∈Set.Ici 1 by simp) hx hx
  norm_num [oddKernelEntropy] at h
  exact h

theorem odd_kernel_phase_shift_bound (s x : ℝ) (hx : 1 ≤ x) :
    oddKernelPhase (s+2) x ≤ oddKernelPhase s x-4*Real.log 2 := by
  rw [odd_kernel_phase_weight_shift]
  linarith [odd_kernel_entropy_lower x hx]

end OddZeta
