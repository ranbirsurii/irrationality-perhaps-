import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter

namespace OddZeta

theorem weighted_gram_double_sum {ι : Type*} (I : Finset ι) (w p q : ι → ℝ) :
    (∑ i ∈ I, w i * p i ^ 2) * (∑ i ∈ I, w i * q i ^ 2) -
      (∑ i ∈ I, w i * p i * q i) ^ 2 =
    (1/2:ℝ) * ∑ i ∈ I, ∑ j ∈ I,
      w i * w j * (p i * q j - q i * p j) ^ 2 := by
  have hs : (∑ i ∈ I, ∑ j ∈ I, w i*w j*(p i*q j-q i*p j)^2) =
      2*((∑ i ∈ I, w i*p i^2)*(∑ j ∈ I, w j*q j^2)-
        (∑ i ∈ I, w i*p i*q i)^2) := by
    calc
      _ = ∑ i ∈ I, ∑ j ∈ I,
          ((w i*p i^2)*(w j*q j^2)+(w i*q i^2)*(w j*p j^2)-
            2*(w i*p i*q i)*(w j*p j*q j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [← Finset.sum_mul]
        ring_nf
        simp only [← Finset.sum_mul]
        ring
  rw [hs]
  ring

theorem log_scalar_cost (mu d a : ℝ) (hm : 0 < mu) (hd : 0 < d) (ha : 0 < a) :
    Real.log (mu*d/a) = Real.log mu + Real.log d - Real.log a := by
  rw [Real.log_div (mul_ne_zero hm.ne' hd.ne') ha.ne', Real.log_mul hm.ne' hd.ne']

theorem moment_cost_common_factor_invariant (D mu nu h : ℝ) (hh : h ≠ 0) :
    (D/h)^2 * mu * (h^2*nu) = D^2*mu*nu := by
  field_simp


theorem reduced_moment_quadratic_bound (a b v h k : ℝ)
    (ha : a ≤ v) (hb : 2 * |b| ≤ v) :
    a*h^2+2*b*h*k+v*k^2 ≤ (3/2:ℝ)*v*(h^2+k^2) := by
  have hv : 0 ≤ v := (by positivity : 0 ≤ 2*|b|).trans hb
  have hcross : 2*b*h*k ≤ |b| * (h^2+k^2) := by
    have h1 := neg_abs_le b
    have h2 := le_abs_self b
    by_cases hh : 0 ≤ h*k
    · nlinarith [sq_nonneg (h-k)]
    · nlinarith [sq_nonneg (h+k)]
  nlinarith [sq_nonneg h, sq_nonneg k]

theorem shifted_polynomial_exp_limit (C k alpha : ℝ) (ha : 0 < alpha) :
    Tendsto (fun n : ℕ => C*((n:ℝ)+1)^k*Real.exp (-alpha*(n:ℝ)))
      atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ)+1)
      tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k alpha ha).comp hx
  have hm := ht.const_mul (C*Real.exp alpha)
  simpa only [mul_zero] using hm.congr (fun n => by
    dsimp
    calc
      _ = C*((n:ℝ)+1)^k * (Real.exp alpha * Real.exp (-alpha*((n:ℝ)+1))) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring)

theorem moment_rhs_limit_of_majorant (R : ℕ → ℝ) (C k alpha : ℝ)
    (ha : 0 < alpha) (hR : ∀ᶠ n in atTop, 0 ≤ R n)
    (hbound : ∀ᶠ n in atTop,
      R n ≤ C*((n:ℝ)+1)^k*Real.exp (-alpha*(n:ℝ))) :
    Tendsto R atTop (nhds 0) := by
  exact squeeze_zero' hR hbound (shifted_polynomial_exp_limit C k alpha ha)

theorem sandwich_limit_of_log_rate (C R : ℕ → ℝ) (delta : ℝ)
    (hd : 0 < delta) (hC : ∀ᶠ n in atTop, 0 < C n)
    (hlog : ∀ᶠ n in atTop, Real.log (C n) ≤ -delta*(n:ℝ))
    (hR : ∀ᶠ n in atTop, 0 ≤ R n)
    (hsand : ∀ᶠ n in atTop, R n ≤ (4/3:ℝ)*C n) :
    Tendsto R atTop (nhds 0) := by
  apply moment_rhs_limit_of_majorant R (4/3) 0 delta hd hR
  filter_upwards [hC,hlog,hsand] with n hc hl hs
  have he : C n ≤ Real.exp (-delta*(n:ℝ)) := by
    calc
      C n = Real.exp (Real.log (C n)) := (Real.exp_log hc).symm
      _ ≤ _ := Real.exp_le_exp.mpr hl
  simpa only [Real.rpow_zero,mul_one] using
    hs.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 4/3))

theorem smallness_of_allowed_exponential_cost
    (sigma decay eta : ℝ) (hgap : sigma+eta < decay)
    (index : ℕ → ℕ) (hi : Tendsto index atTop atTop)
    (D W S L : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n) (hW : ∀ n, 0 ≤ W n)
    (hb : ∀ᶠ n in atTop, |L n| ≤ D n*W n*S n)
    (hd : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      D n ≤ Real.exp ((sigma+e)*(index n:ℝ)))
    (hw : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      W n ≤ Real.exp ((eta+e)*(index n:ℝ)))
    (hs : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      S n ≤ Real.exp ((-decay+e)*(index n:ℝ))) :
    Tendsto L atTop (nhds 0) := by
  let e : ℝ := (decay-sigma-eta)/6
  have he : 0 < e := by dsimp [e]; linarith
  have hg : 0 < (decay-sigma-eta)/2 := by linarith
  have hm : ∀ᶠ n in atTop,
      |L n| ≤ Real.exp (-((decay-sigma-eta)/2)*(index n:ℝ)) := by
    filter_upwards [hb,hd e he,hw e he,hs e he] with n h hn hw' hs'
    have hp := mul_le_mul hn hw' (hW n) (Real.exp_pos _).le
    calc
      |L n| ≤ D n*W n*S n := h
      _ ≤ D n*W n*Real.exp ((-decay+e)*(index n:ℝ)) :=
        mul_le_mul_of_nonneg_left hs' (mul_nonneg (hD n) (hW n))
      _ ≤ (Real.exp ((sigma+e)*(index n:ℝ))*
          Real.exp ((eta+e)*(index n:ℝ)))*Real.exp ((-decay+e)*(index n:ℝ)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [e]
        ring
  have ht : Tendsto (fun n => Real.exp (-((decay-sigma-eta)/2)*(index n:ℝ)))
      atTop (nhds 0) := by
    have ha := Tendsto.const_mul_atTop hg (tendsto_natCast_atTop_atTop.comp hi)
    simpa only [Function.comp_def,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp ha
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.1 ht) eps heps
  obtain ⟨M,hM⟩ := eventually_atTop.1 hm
  refine ⟨max N M, ?_⟩
  intro n hn
  have hx := hN n (le_trans (le_max_left _ _) hn)
  have hy := hM n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq,sub_zero] at hx ⊢
  exact hy.trans_lt ((le_abs_self _).trans_lt hx)

theorem weighted_prefix_energy_le {ι : Type*} (I : Finset ι)
    (w p : ι → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hP : 0 < ∑ i ∈ I, w i) :
    (∑ i ∈ I, w i*p i)^2/(∑ i ∈ I, w i) ≤ ∑ i ∈ I, w i*p i^2 := by
  have hid := weighted_gram_double_sum I w p (fun _ => 1)
  simp only [one_pow,mul_one,one_mul] at hid
  have hn : 0 ≤ (1/2:ℝ)*∑ i ∈ I, ∑ j ∈ I,
      w i*w j*(p i-p j)^2 := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)
  rw [← hid] at hn
  apply (div_le_iff₀ hP).2
  nlinarith

theorem signed_prefix_cauchy (P T a b E : ℝ)
    (hP : 0 < P) (hT : 0 < T) (hb : b^2 ≤ T*E) :
    (a+b)^2 ≤ (P+T)*(a^2/P+E) := by
  have ht : 0 ≤ E-b^2/T := by
    have h : b^2/T ≤ E := (div_le_iff₀ hT).2 (by simpa [mul_comm] using hb)
    linarith
  have hn := add_nonneg
    (div_nonneg (sq_nonneg (T*a-P*b)) (mul_pos hP hT).le)
    (mul_nonneg (add_pos hP hT).le ht)
  have hid : (T*a-P*b)^2/(P*T)+(P+T)*(E-b^2/T) =
      (P+T)*(a^2/P+E)-(a+b)^2 := by
    field_simp
    <;> ring
  rw [hid] at hn
  linarith

theorem signed_prefix_energy_gain (P T a b : ℝ)
    (hP : 0 < P) (hT : 0 < T) :
    a^2/P+b^2/T-(a+b)^2/(P+T) =
      (T*a-P*b)^2/(P*T*(P+T)) := by
  have hsum : P+T ≠ 0 := (add_pos hP hT).ne'
  field_simp
  <;> ring

theorem signed_prefix_merge_le (P T a b : ℝ)
    (hP : 0 < P) (hT : 0 < T) :
    (a+b)^2/(P+T) ≤ a^2/P+b^2/T := by
  have h := div_nonneg (sq_nonneg (T*a-P*b))
    (mul_pos (mul_pos hP hT) (add_pos hP hT)).le
  rw [← signed_prefix_energy_gain P T a b hP hT] at h
  linarith

theorem prefix_tail_power_budget (E B K p t : ℝ)
    (hK : 0 < K) (ht : K ≤ t) (hB : 0 ≤ B)
    (hbudget : B ≤ (E-p)*K) :
    -E/t+B/t^2 ≤ -p/t := by
  have htpos : 0 < t := hK.trans_le ht
  have hep : 0 ≤ E-p := by nlinarith
  have hbt : B ≤ (E-p)*t := hbudget.trans (mul_le_mul_of_nonneg_left ht hep)
  apply (le_of_sub_nonneg : 0 ≤ -p/t-(-E/t+B/t^2) → _)
  have hid : -p/t-(-E/t+B/t^2)=((E-p)*t-B)/t^2 := by
    field_simp
    <;> ring
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr hbt) (sq_nonneg t)

theorem prefix_positive_pole_ratio (K t h : ℝ)
    (hK : h < K) (ht : K ≤ t) (hh : 0 ≤ h) :
    t/(t-h) ≤ K/(K-h) := by
  apply (div_le_div_iff₀ (by linarith : 0 < t-h) (by linarith : 0 < K-h)).2
  nlinarith [mul_nonneg hh (sub_nonneg.mpr ht)]

theorem prefix_negative_pole_ratio (K t h : ℝ)
    (hK : 0 < K) (ht : K ≤ t) (hh : 0 ≤ h) :
    K/(K+h) ≤ t/(t+h) := by
  apply (div_le_div_iff₀ (by linarith : 0 < K+h) (by linarith : 0 < t+h)).2
  nlinarith [mul_nonneg hh (sub_nonneg.mpr ht)]

theorem signed_prefix_rank_one_determinant (h11 h12 h22 q1 q2 P : ℝ) :
    (h11+q1^2/P)*(h22+q2^2/P)-(h12+q1*q2/P)^2 =
      h11*h22-h12^2+(q1^2*h22-2*q1*q2*h12+q2^2*h11)/P := by
  ring

theorem near_prefix_tail_rate_positive (s : ℕ) (hs : 7 ≤ s) :
    1 < (s:ℝ)*(5/4)*Real.log (9/5:ℝ)-1-(5/4)*Real.log 5 := by
  have hl := Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ)<4/5)
  norm_num at hl
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have h54 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<5/4)
  rw [Real.log_div (by norm_num : (5:ℝ)≠0) (by norm_num : (4:ℝ)≠0)] at h54
  have h4 : Real.log 4=2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  have h5 : Real.log 5 ≤ (9:ℝ)/4 := by rw [h4] at h54; linarith
  have hsr : (7:ℝ) ≤ s := by exact_mod_cast hs
  have hg := mul_nonneg (sub_nonneg.mpr hsr)
    (show 0 ≤ Real.log (9/5:ℝ) by linarith)
  nlinarith

theorem log_sandwich_rate_gap (C R : ℝ) (n : ℕ)
    (hn : 0 < n) (hC : 0 < C) (hl : C ≤ R) (hu : R ≤ (4/3:ℝ)*C) :
    0 ≤ (Real.log R-Real.log C)/(n:ℝ) ∧
      (Real.log R-Real.log C)/(n:ℝ) ≤ Real.log (4/3:ℝ)/(n:ℝ) := by
  have hR : 0 < R := hC.trans_le hl
  have hlow := Real.log_le_log hC hl
  have hhigh := Real.log_le_log hR hu
  rw [Real.log_mul (by norm_num : (4/3:ℝ) ≠ 0) hC.ne'] at hhigh
  have hnr : (0:ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlow) hnr
  · exact div_le_div_of_nonneg_right (by linarith) hnr

theorem log_sandwich_rate_gap_tends_zero (C R : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, 0 < C n)
    (hl : ∀ᶠ n in atTop, C n ≤ R n)
    (hu : ∀ᶠ n in atTop, R n ≤ (4/3:ℝ)*C n) :
    Tendsto (fun n => (Real.log (R n)-Real.log (C n))/(n:ℝ))
      atTop (nhds 0) := by
  have hb : ∀ᶠ n in atTop,
      0 ≤ (Real.log (R n)-Real.log (C n))/(n:ℝ) ∧
      (Real.log (R n)-Real.log (C n))/(n:ℝ) ≤ Real.log (4/3:ℝ)/(n:ℝ) := by
    filter_upwards [hC,hl,hu,eventually_ge_atTop 1] with n hc hlo hup hn
    exact log_sandwich_rate_gap (C n) (R n) n (by omega) hc hlo hup
  exact squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log (4/3:ℝ)))

theorem adaptive_prefix_quadratic_bound (mu P a E B delta : ℝ)
    (hP : 0 < P) (hmu : 0 ≤ mu) (hd : 0 ≤ delta)
    (hB : 0 ≤ B+delta) (ha : |a| ≤ B+delta)
    (hratio : mu/P ≤ 1+delta) (htail : mu*E ≤ delta) :
    mu*(a^2/P+E) ≤ (1+delta)*(B+delta)^2+delta := by
  have hs : a^2 ≤ (B+delta)^2 := by
    have h := mul_self_le_mul_self (abs_nonneg a) ha
    nlinarith [sq_abs a]
  have hm := mul_le_mul hratio hs (sq_nonneg a) (by linarith : 0 ≤ 1+delta)
  calc
    _ = (mu/P)*a^2+mu*E := by ring
    _ ≤ _ := add_le_add hm htail

theorem adaptive_prefix_unit_margin (e : ℝ) (he : 0 < e) (hupper : e ≤ 1) :
    (1+e/16)*(1-e+e/16)^2+e/16 ≤ 1-e/2 := by
  have hx : 0 ≤ 1-e+e/16 := by linarith
  have hs : (1-e+e/16)^2 ≤ 1-3*e/4 := by
    have hm := mul_self_le_mul_self hx (show 1-e+e/16 ≤ 1-e/2 by linarith)
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hupper)]
  have hs1 : (1-e+e/16)^2 ≤ 1 := by linarith
  have ht := mul_nonneg (show 0 ≤ e/16 by positivity) (sub_nonneg.mpr hs1)
  nlinarith

theorem adaptive_prefix_seed_margin (B : ℝ) (hB : 0 < B) (hu : B ≤ 1) :
    (1+B^2/16)*(B+B^2/16)^2+B^2/16 ≤ 2*B^2 := by
  have hsq : B^2 ≤ B := by nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hu)]
  have hs1 : B^2 ≤ 1 := by nlinarith
  have hx : B+B^2/16 ≤ (17/16:ℝ)*B := by linarith
  have hxsq := mul_self_le_mul_self (show 0 ≤ B+B^2/16 by positivity) hx
  have hs : (B+B^2/16)^2 ≤ (17/16:ℝ)^2*B^2 := by nlinarith
  have hm := mul_le_mul (show 1+B^2/16 ≤ (17/16:ℝ) by linarith)
    hs (sq_nonneg (B+B^2/16)) (by norm_num : (0:ℝ) ≤ 17/16)
  nlinarith [sq_nonneg B]

theorem geometric_weight_seed_cap (s : ℕ) (hs : 7 ≤ s) :
    2*((3/2:ℝ)*(2/3:ℝ)^s)^2 < (1/64:ℝ) := by
  have hi : s=7+(s-7) := by omega
  have hp : (2/3:ℝ)^(s-7) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hb : (3/2:ℝ)*(2/3:ℝ)^s ≤ (64/729:ℝ) := by
    rw [hi,pow_add]
    norm_num at hp ⊢
    nlinarith
  have hpos : (0:ℝ) ≤ (3/2:ℝ)*(2/3:ℝ)^s := by positivity
  have hsq := mul_self_le_mul_self hpos hb
  nlinarith

theorem geometric_prefix_log_bound (s : ℕ) (hs : 7 ≤ s) (R : ℝ)
    (hR : 0 < R) (hb : R ≤ 2*((3/2:ℝ)*(2/3:ℝ)^s)^2) :
    Real.log R < -Real.log 64 := by
  have hlog := Real.log_lt_log hR (hb.trans_lt (geometric_weight_seed_cap s hs))
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (64:ℝ) ≠ 0),
    Real.log_one,zero_sub] at hlog
  exact hlog

theorem adjacent_integer_form_bounds (x e : ℝ)
    (hl : 1+e ≤ x) (hu : x ≤ 2-e) :
    |x-1| ≤ 1-e ∧ |x-2| ≤ 1-e := by
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem adaptive_prefix_log_negative (R e : ℝ)
    (hR : 0 < R) (he : 0 < e) (hbound : R ≤ 1-e/2) :
    Real.log R < 0 := by
  exact Real.log_neg hR (by linarith)

theorem bounded_cost_nonpositive_upper_rate (R : ℕ → ℝ) (B : ℝ)
    (hB : 0 < B) (hR : ∀ᶠ n in atTop, 0 < R n)
    (hb : ∀ᶠ n in atTop, R n ≤ B) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, Real.log (R n)/(n:ℝ) ≤ eps := by
  intro eps heps
  have hs : ∀ᶠ n : ℕ in atTop, Real.log B/(n:ℝ) < eps :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log B)).eventually
      (gt_mem_nhds heps)
  filter_upwards [hR,hb,hs] with n hr hbound hsmall
  have hlog := Real.log_le_log hr hbound
  exact (div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)).trans hsmall.le

theorem signed_prefix_certificate_sharp (L P e : ℝ) (h : |L-P| ≤ e) :
    |L| ≤ |P|+e ∧ |P|+e ≤ |L|+2*e := by
  have h1 : |L| ≤ |L-P|+|P| := by
    simpa using abs_add_le (L-P) P
  have h2 : |P| ≤ |L-P|+|L| := by
    have h2 := abs_add_le (P-L) L
    simpa only [sub_add_cancel, abs_sub_comm P L] using h2
  constructor <;> linarith

end OddZeta
