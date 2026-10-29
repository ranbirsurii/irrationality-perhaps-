import OddZeta.BinaryGaussMinimum
import Mathlib.Tactic.FieldSimp

namespace OddZeta

theorem unimodular_integer_preimage (a b c d : ℤ)
    (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1) (x y : ℤ) :
    ∃ u v : ℤ, a * u + b * v = x ∧ c * u + d * v = y := by
  rcases hdet with h | h
  · refine ⟨d * x - b * y, a * y - c * x, ?_, ?_⟩
    · calc
        _ = (a * d - b * c) * x := by ring
        _ = x := by rw [h]; ring
    · calc
        _ = (a * d - b * c) * y := by ring
        _ = y := by rw [h]; ring
  · refine ⟨b * y - d * x, c * x - a * y, ?_, ?_⟩
    · calc
        _ = -(a * d - b * c) * x := by ring
        _ = x := by rw [h]; ring
    · calc
        _ = -(a * d - b * c) * y := by ring
        _ = y := by rw [h]; ring

theorem binary_change_of_variables (A B C a b c d x y : ℝ) :
    binaryQuadratic A B C (a * x + b * y) (c * x + d * y) =
      binaryQuadratic (binaryQuadratic A B C a c)
        (A * a * b + B * (a * d + b * c) + C * c * d)
        (binaryQuadratic A B C b d) x y := by
  unfold binaryQuadratic
  ring

theorem binary_certificate_first_minimum (A B C mu beta nu : ℝ)
    (a b c d : ℤ)
    (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (hfirst : mu = binaryQuadratic A B C a c)
    (hcross : beta = A * a * b + B * ((a : ℝ) * d + (b : ℝ) * c) + C * c * d)
    (hsecond : nu = binaryQuadratic A B C b d)
    (hmu : 0 < mu) (horder : mu ≤ nu) (hbeta : 2 * |beta| ≤ mu)
    (x y : ℤ) (hne : x ≠ 0 ∨ y ≠ 0) :
    mu ≤ binaryQuadratic A B C x y := by
  obtain ⟨u, v, hx, hy⟩ := unimodular_integer_preimage a b c d hdet x y
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_cases hu : u = 0
    · right
      intro hv
      have hxx : x = 0 := by simpa [hu, hv] using hx.symm
      have hyy : y = 0 := by simpa [hu, hv] using hy.symm
      exact hne.elim (fun h => h hxx) (fun h => h hyy)
    · exact Or.inl hu
  have hxR : (a : ℝ) * u + (b : ℝ) * v = x := by exact_mod_cast hx
  have hyR : (c : ℝ) * u + (d : ℝ) * v = y := by exact_mod_cast hy
  calc
    mu ≤ binaryQuadratic mu beta nu u v :=
      reduced_binary_first_minimum mu beta nu hmu horder hbeta u v huv
    _ = binaryQuadratic A B C ((a : ℝ) * u + (b : ℝ) * v)
        ((c : ℝ) * u + (d : ℝ) * v) := by
      rw [binary_change_of_variables, ← hfirst, ← hcross, ← hsecond]
    _ = _ := by rw [hxR, hyR]

theorem binary_certificate_independent_pair_minimum (A B C mu beta nu : ℝ)
    (a b c d : ℤ)
    (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (hfirst : mu = binaryQuadratic A B C a c)
    (hcross : beta = A * a * b + B * ((a : ℝ) * d + (b : ℝ) * c) + C * c * d)
    (hsecond : nu = binaryQuadratic A B C b d)
    (hmu : 0 < mu) (horder : mu ≤ nu) (hbeta : 2 * |beta| ≤ mu)
    (p q r s : ℤ) (hpairs : p * s - q * r ≠ 0) :
    nu ≤ max (binaryQuadratic A B C p q) (binaryQuadratic A B C r s) := by
  obtain ⟨u, v, hp, hq⟩ := unimodular_integer_preimage a b c d hdet p q
  obtain ⟨w, z, hr, hs⟩ := unimodular_integer_preimage a b c d hdet r s
  have hpair : u * z - v * w ≠ 0 := by
    intro hzero
    apply hpairs
    calc
      p * s - q * r =
          (a * u + b * v) * (c * w + d * z) -
          (c * u + d * v) * (a * w + b * z) := by rw [hp, hq, hr, hs]
      _ = (a * d - b * c) * (u * z - v * w) := by ring
      _ = 0 := by rw [hzero]; ring
  have hfirstPair : binaryQuadratic mu beta nu u v = binaryQuadratic A B C p q := by
    have hpR : (a : ℝ) * u + (b : ℝ) * v = p := by exact_mod_cast hp
    have hqR : (c : ℝ) * u + (d : ℝ) * v = q := by exact_mod_cast hq
    rw [hfirst, hcross, hsecond, ← binary_change_of_variables, hpR, hqR]
  have hsecondPair : binaryQuadratic mu beta nu w z = binaryQuadratic A B C r s := by
    have hrR : (a : ℝ) * w + (b : ℝ) * z = r := by exact_mod_cast hr
    have hsR : (c : ℝ) * w + (d : ℝ) * z = s := by exact_mod_cast hs
    rw [hfirst, hcross, hsecond, ← binary_change_of_variables, hrR, hsR]
  have h := reduced_binary_independent_pair_minimum mu beta nu hmu horder hbeta u v w z hpair
  simpa only [hfirstPair, hsecondPair] using h

theorem binary_certificate_attainment (A B C mu nu : ℝ) (a b c d : ℤ)
    (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (hfirst : mu = binaryQuadratic A B C a c)
    (hsecond : nu = binaryQuadratic A B C b d) :
    ∃ x y z t : ℤ, x * t - y * z ≠ 0 ∧
      binaryQuadratic A B C x y = mu ∧ binaryQuadratic A B C z t = nu := by
  refine ⟨a, c, b, d, ?_, hfirst.symm, hsecond.symm⟩
  rcases hdet with h | h
  · rw [mul_comm c b, h]
    norm_num
  · rw [mul_comm c b, h]
    norm_num

theorem binary_pullback_determinant (A B C a b c d : ℝ) :
    binaryQuadratic A B C a c * binaryQuadratic A B C b d -
      (A*a*b+B*(a*d+b*c)+C*c*d)^2 =
      (a*d-b*c)^2*(A*C-B^2) := by
  unfold binaryQuadratic
  ring

theorem unimodular_nonzero_pair (a b c d x y : ℤ)
    (hd : a*d-b*c=1 ∨ a*d-b*c= -1) (hxy : x ≠ 0 ∨ y ≠ 0) :
    a*x+b*y ≠ 0 ∨ c*x+d*y ≠ 0 := by
  have hdn : a*d-b*c ≠ 0 := by rcases hd with h | h <;> rw [h] <;> norm_num
  by_cases hfirst : a*x+b*y=0
  · right
    intro hsecond
    have hx : (a*d-b*c)*x=0 := by
      calc
        _ = d*(a*x+b*y)-b*(c*x+d*y) := by ring
        _ = 0 := by rw [hfirst,hsecond]; ring
    have hy : (a*d-b*c)*y=0 := by
      calc
        _ = a*(c*x+d*y)-c*(a*x+b*y) := by ring
        _ = 0 := by rw [hfirst,hsecond]; ring
    exact hxy.elim
      (fun h => h ((mul_eq_zero.mp hx).resolve_left hdn))
      (fun h => h ((mul_eq_zero.mp hy).resolve_left hdn))
  · exact Or.inl hfirst

theorem binary_unimodular_lower_bound_iff (A B C : ℝ) (a b c d : ℤ) (m : ℝ)
    (hd : a*d-b*c=1 ∨ a*d-b*c= -1) :
    (∀ x y : ℤ, x ≠ 0 ∨ y ≠ 0 → m ≤ binaryQuadratic A B C x y) ↔
    (∀ u v : ℤ, u ≠ 0 ∨ v ≠ 0 →
      m ≤ binaryQuadratic A B C ((a:ℝ)*u+b*v) ((c:ℝ)*u+d*v)) := by
  constructor
  · intro h u v huv
    have hz := unimodular_nonzero_pair a b c d u v hd huv
    have hr := h (a*u+b*v) (c*u+d*v) hz
    simpa only [Int.cast_add,Int.cast_mul] using hr
  · intro h x y hxy
    obtain ⟨u,v,hx,hy⟩ := unimodular_integer_preimage a b c d hd x y
    have huv : u ≠ 0 ∨ v ≠ 0 := by
      by_cases hu : u=0
      · right
        intro hv
        have hx0 : x=0 := by simpa [hu,hv] using hx.symm
        have hy0 : y=0 := by simpa [hu,hv] using hy.symm
        exact hxy.elim (fun h => h hx0) (fun h => h hy0)
      · exact Or.inl hu
    have hxR : (a:ℝ)*u+b*v=x := by exact_mod_cast hx
    have hyR : (c:ℝ)*u+d*v=y := by exact_mod_cast hy
    simpa only [hxR,hyR] using h u v huv

theorem quadratic_ideal_norm_identity (a b c x y : ℝ) :
    (a*x+b*y/2)^2+(4*a*c-b^2)*(y/2)^2 =
      a*(a*x^2+b*x*y+c*y^2) := by ring

theorem scaled_primitive_gram_determinant (eta a b c : ℝ) :
    (eta*a)*(eta*c)-(eta*b/2)^2 = eta^2*(4*a*c-b^2)/4 := by ring

theorem primitive_integer_value_floor (a b c x y : ℤ) (eta : ℝ)
    (heta : 0 ≤ eta) (hp : 0 < a*x^2+b*x*y+c*y^2) :
    eta ≤ eta*((a:ℝ)*x^2+b*x*y+c*y^2) := by
  have hi : (1:ℤ) ≤ a*x^2+b*x*y+c*y^2 := by omega
  have hr : (1:ℝ) ≤ (a:ℝ)*x^2+b*x*y+c*y^2 := by exact_mod_cast hi
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hr heta

theorem binary_schur_square (A B C x y : ℝ) (hA : A ≠ 0) :
    binaryQuadratic A B C x y =
      A*(x+B/A*y)^2+(A*C-B^2)/A*y^2 := by
  unfold binaryQuadratic
  field_simp
  <;> ring

theorem binary_schur_large_second_coordinate (A B C T x y : ℝ)
    (hA : 0 < A) (hlarge : T ≤ (A*C-B^2)/A*y^2) :
    T ≤ binaryQuadratic A B C x y := by
  rw [binary_schur_square A B C x y hA.ne']
  exact hlarge.trans (le_add_of_nonneg_left (mul_nonneg hA.le (sq_nonneg _)))

theorem binary_schur_small_coordinate_test (A B C T x y : ℝ)
    (hA : 0 < A)
    (hgap : (T-(A*C-B^2)/A*y^2)/A ≤ (x+B/A*y)^2) :
    T ≤ binaryQuadratic A B C x y := by
  have h := (div_le_iff₀ hA).mp hgap
  rw [binary_schur_square A B C x y hA.ne']
  nlinarith

theorem schur_shift_perturbation (x theta xi v : ℝ) :
    |(|x+theta*v|-|x+xi*v|)| ≤ |theta-xi| * |v| := by
  calc
    _ ≤ |(x+theta*v)-(x+xi*v)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = _ := by rw [show (x+theta*v)-(x+xi*v)=(theta-xi)*v by ring,abs_mul]

theorem schur_uniform_range_perturbation (x theta xi v d V : ℝ)
    (hd : 0 ≤ d) (hslope : |theta-xi| ≤ d) (hv : |v| ≤ V) :
    |(|x+theta*v|-|x+xi*v|)| ≤ d*V := by
  exact (schur_shift_perturbation x theta xi v).trans
    (mul_le_mul hslope hv (abs_nonneg v) hd)

theorem schur_variable_point_bound (A h theta u v V : ℝ)
    (hA : 0 ≤ A) (hh : 0 ≤ h) (hV : 0 < V)
    (he : |u+theta*v| ≤ 1/V) (hv : |v| ≤ V) :
    A*(u+theta*v)^2+h*v^2 ≤ A/V^2+h*V^2 := by
  have he2 := mul_self_le_mul_self (abs_nonneg (u+theta*v)) he
  have hv2 := mul_self_le_mul_self (abs_nonneg v) hv
  have heq : (u+theta*v)^2 ≤ (1/V)^2 := by nlinarith [sq_abs (u+theta*v)]
  have hvq : v^2 ≤ V^2 := by nlinarith [sq_abs v]
  have hp := add_le_add (mul_le_mul_of_nonneg_left heq hA)
    (mul_le_mul_of_nonneg_left hvq hh)
  calc
    _ ≤ A*(1/V)^2+h*V^2 := hp
    _ = _ := by field_simp

theorem variable_point_balance_identity (h H V : ℝ) (hH : H ≠ 0) (hV : V ≠ 0) :
    h*H^4/V^2+h*V^2 = h*H^2*((V/H)^2+(H/V)^2) := by
  field_simp
  <;> ring

theorem continued_fraction_local_gap_bound (qprev q a : ℝ)
    (hq : 0 < q) (hp : qprev ≤ q) :
    (a*q+qprev)/q ≤ a+1 := by
  apply (div_le_iff₀ hq).2
  nlinarith

theorem nearest_denominator_balance_bound (q Q W : ℝ)
    (hq : 0 < q) (hQ : 0 < Q) (hW : 0 < W)
    (hl : q^2 ≤ W) (hu : W ≤ Q^2) :
    min (q^2/W+W/q^2) (Q^2/W+W/Q^2) ≤ 2*(Q/q) := by
  have hqQ : q ≤ Q := by nlinarith
  have hg : 1 ≤ Q/q := (le_div_iff₀ hq).2 (by simpa using hqQ)
  by_cases hm : W ≤ q*Q
  · have h1 : q^2/W ≤ 1 := (div_le_one hW).2 hl
    have h2 : W/q^2 ≤ Q/q := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hq) hq).2
      nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hm)]
    exact (min_le_left _ _).trans (by linarith)
  · have hm' : q*Q ≤ W := le_of_not_ge hm
    have h1 : Q^2/W ≤ Q/q := by
      apply (div_le_div_iff₀ hW hq).2
      nlinarith [mul_nonneg hQ.le (sub_nonneg.mpr hm')]
    have h2 : W/Q^2 ≤ 1 := (div_le_one (sq_pos_of_pos hQ)).2 hu
    exact (min_le_right _ _).trans (by linarith)

end OddZeta
