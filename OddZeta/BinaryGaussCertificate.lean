import OddZeta.BinaryGaussMinimum

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

end OddZeta
