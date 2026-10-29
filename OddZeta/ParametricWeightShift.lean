import OddZeta.PoisedKernelPositivity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.RingTheory.Binomial

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

theorem saalschutz_entropy_stationary_factor (beta x : ℝ) :
    (beta-x)*(1+x)-x*(1+beta+x)=beta-2*x-2*x^2 := by ring

theorem saalschutz_entropy_strict_concavity (beta x : ℝ)
    (hx : 0 < x) (hb : x < beta) :
    -1/(beta-x)-1/(1+beta+x)+1/(1+x)-1/x < 0 := by
  have h1 : 0 < (1:ℝ)/(beta-x) := one_div_pos.mpr (by linarith)
  have h2 : 0 < (1:ℝ)/(1+beta+x) := one_div_pos.mpr (by linarith)
  have h3 : (1:ℝ)/(1+x)<1/x := by
    apply (div_lt_div_iff₀ (by linarith : 0 < 1+x) hx).2
    nlinarith
  simp only [neg_div]
  linarith

theorem saalschutz_half_radius_identity (t : ℝ) :
    (1+t)^4-16*t*(1-t)^2=(t^2-6*t+1)^2 := by ring

theorem saalschutz_half_entropy_value (t : ℝ) (ht : 0 < t) (hu : t < 1)
    (hsaddle : t^2-6*t+1=0) :
    2*Real.log (1+t)-Real.log (1-t)-(1/2:ℝ)*Real.log t=Real.log 4 := by
  have heq : (1+t)^4=16*t*(1-t)^2 := by
    have h := saalschutz_half_radius_identity t
    rw [hsaddle] at h
    nlinarith
  have hlog := congrArg Real.log heq
  rw [Real.log_pow,Real.log_mul (by positivity : (16:ℝ)*t ≠ 0)
    (by positivity : (1-t)^2 ≠ 0),
    Real.log_mul (by norm_num : (16:ℝ) ≠ 0) ht.ne',Real.log_pow] at hlog
  have h16 : Real.log 16=2*Real.log 4 := by
    convert Real.log_pow (4:ℝ) 2 using 1 <;> norm_num
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem saalschutz_signed_binomial_mass (n m : ℕ) :
    (∑ ij ∈ Finset.antidiagonal m,
      Ring.choose ((n+2*m+1:ℕ):ℤ) ij.1 *
        Ring.choose (-((n+1:ℕ):ℤ)) ij.2) = ((2*m).choose m:ℤ) := by
  rw [← Ring.add_choose_eq m (Commute.all _ _)]
  have h : ((n+2*m+1:ℕ):ℤ)+ -((n+1:ℕ):ℤ)=((2*m:ℕ):ℤ) := by omega
  rw [h,Ring.choose_natCast]

theorem saalschutz_signed_shifted_mass (n m k : ℕ) (hk : k ≤ m) :
    (∑ ij ∈ Finset.antidiagonal (m-k),
      Ring.choose ((n+2*m+1:ℕ):ℤ) ij.1 *
        Ring.choose (-((n+k+1:ℕ):ℤ)) ij.2) = ((2*m-k).choose (m-k):ℤ) := by
  rw [← Ring.add_choose_eq (m-k) (Commute.all _ _)]
  have h : ((n+2*m+1:ℕ):ℤ)+ -((n+k+1:ℕ):ℤ)=((2*m-k:ℕ):ℤ) := by omega
  rw [h,Ring.choose_natCast]

theorem generalized_binomial_backward_step (x : ℚ) (N : ℕ) :
    Ring.choose (x-1) (N+1)-Ring.choose x (N+1)= -Ring.choose (x-1) N := by
  have h := Ring.choose_succ_succ (x-1) N
  rw [show x-1+1=x by ring] at h
  linarith

noncomputable def binomialBackwardDifference : ℕ → ℕ → ℚ → ℚ
  | 0,N,x => Ring.choose x N
  | k+1,N,x => binomialBackwardDifference k N (x-1)-binomialBackwardDifference k N x

theorem binomial_backward_difference_closed (k N : ℕ) (hk : k ≤ N) (x : ℚ) :
    binomialBackwardDifference k N x = (-1:ℚ)^k*Ring.choose (x-k) (N-k) := by
  induction k generalizing N x with
  | zero => simp [binomialBackwardDifference]
  | succ k ih =>
    have hk' : k ≤ N := by omega
    rw [binomialBackwardDifference,ih N hk' (x-1),ih N hk' x]
    have hN : N-k=(N-(k+1))+1 := by omega
    rw [hN,show (x-1)-(k:ℚ)=(x-k)-1 by ring,← mul_sub,
      generalized_binomial_backward_step]
    have hx : x-((k+1:ℕ):ℚ)=(x-k)-1 := by push_cast; ring
    rw [hx,pow_succ]
    ring

end OddZeta
