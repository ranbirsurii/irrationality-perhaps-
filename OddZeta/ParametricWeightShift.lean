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

noncomputable def sharpOddDecay (s : ℕ) : ℝ :=
  Real.log 2397+((s:ℝ)-7)*Real.log 4

theorem sharp_odd_decay_allowance (s : ℕ) (hs : 7 ≤ s) :
    (s:ℝ)+1/3 < sharpOddDecay s := by
  have htwo : (2:ℝ)/3 < Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ)<1)
    norm_num only [mul_one, show (1:ℝ)+2=3 by norm_num,
      show (1:ℝ)+1=2 by norm_num] at h
    exact h
  have hbase : 11*Real.log 2 < Real.log 2397 := by
    have h := Real.log_lt_log (by norm_num : (0:ℝ)<2^11)
      (by norm_num : (2:ℝ)^11<2397)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have hfour : Real.log 4=2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  have hsr : (7:ℝ) ≤ s := by exact_mod_cast hs
  have hp : 0 ≤ ((s:ℝ)-7)*(Real.log 4-1) :=
    mul_nonneg (by linarith) (by rw [hfour]; linarith)
  have heq : sharpOddDecay s-(s:ℝ) =
      (Real.log 2397-7)+((s:ℝ)-7)*(Real.log 4-1) := by
    unfold sharpOddDecay
    ring
  linarith

theorem sharp_odd_decay_three_quarters (s : ℕ) (hs : 7 ≤ s) :
    (s:ℝ)+3/4 < sharpOddDecay s := by
  have h1 := Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ)<1/4)
  have h2 := Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ)<1/5)
  have h3 := Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ)<1/6)
  have h4 := Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ)<1/7)
  norm_num at h1 h2 h3 h4
  have hl4 : Real.log 4=2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  have hl8 : Real.log 8=3*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 3 using 1 <;> norm_num
  have hsum : Real.log ((5:ℝ)/4)+Real.log ((6:ℝ)/5)+
      Real.log ((7:ℝ)/6)+Real.log ((8:ℝ)/7)=Real.log 2 := by
    rw [Real.log_div (by norm_num : (5:ℝ)≠0) (by norm_num : (4:ℝ)≠0),
      Real.log_div (by norm_num : (6:ℝ)≠0) (by norm_num : (5:ℝ)≠0),
      Real.log_div (by norm_num : (7:ℝ)≠0) (by norm_num : (6:ℝ)≠0),
      Real.log_div (by norm_num : (8:ℝ)≠0) (by norm_num : (7:ℝ)≠0),hl4,hl8]
    ring
  have htwo : (2:ℝ)/9+2/11+2/13+2/15 < Real.log 2 := by linarith
  have hr := Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ)<349/2048)
  norm_num at hr
  rw [Real.log_div (by norm_num : (2397:ℝ)≠0) (by norm_num : (2048:ℝ)≠0)] at hr
  have hl2048 : Real.log 2048=11*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 11 using 1 <;> norm_num
  rw [hl2048] at hr
  have hbase : (31:ℝ)/4 < Real.log 2397 := by linarith
  have hsr : (7:ℝ) ≤ s := by exact_mod_cast hs
  have hp : 0 ≤ ((s:ℝ)-7)*(Real.log 4-1) :=
    mul_nonneg (by linarith) (by rw [hl4]; linarith)
  have heq : sharpOddDecay s-(s:ℝ) =
      (Real.log 2397-7)+((s:ℝ)-7)*(Real.log 4-1) := by
    unfold sharpOddDecay
    ring
  linarith

end OddZeta
