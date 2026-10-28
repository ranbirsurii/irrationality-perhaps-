import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring

namespace OddZeta

def cubicFrame0 (a b c s1 s2 s3 x0 x1 x2 x3 : ℤ) : ℤ :=
  -a*b*c*x0+a*b*s1*x1-a*s2*x2+s3*x3
def cubicFrame1 (a b c s1 s2 x0 x1 x2 : ℤ) : ℤ :=
  (a*b+a*c+b*c)*x0-(a+b)*s1*x1+s2*x2
def cubicFrame2 (a b c s1 x0 x1 : ℤ) : ℤ :=
  -(a+b+c)*x0+s1*x1

theorem cubic_frame_inverse_first (a b c s1 x0 x1 : ℤ) :
    cubicFrame2 a b c s1 x0 x1+(a+b+c)*x0 = s1*x1 := by
  unfold cubicFrame2
  ring

theorem cubic_frame_inverse_second (a b c s1 s2 x0 x1 x2 : ℤ) :
    cubicFrame1 a b c s1 s2 x0 x1 x2+
      (a+b)*cubicFrame2 a b c s1 x0 x1+(a^2+a*b+b^2)*x0 = s2*x2 := by
  unfold cubicFrame1 cubicFrame2
  ring

theorem cubic_frame_inverse_third (a b c s1 s2 s3 x0 x1 x2 x3 : ℤ) :
    cubicFrame0 a b c s1 s2 s3 x0 x1 x2 x3+
      a*cubicFrame1 a b c s1 s2 x0 x1 x2+
      a^2*cubicFrame2 a b c s1 x0 x1+a^3*x0 = s3*x3 := by
  unfold cubicFrame0 cubicFrame1 cubicFrame2
  ring

theorem cubic_frame_divisibility_iff (a b c s1 s2 s3 x0 x1 x2 x3 d : ℤ) :
    (d ∣ cubicFrame0 a b c s1 s2 s3 x0 x1 x2 x3) ∧
      (d ∣ cubicFrame1 a b c s1 s2 x0 x1 x2) ∧
      (d ∣ cubicFrame2 a b c s1 x0 x1) ∧ (d ∣ x0) ↔
      (d ∣ x0) ∧ (d ∣ s1*x1) ∧ (d ∣ s2*x2) ∧ (d ∣ s3*x3) := by
  constructor
  · rintro ⟨h0,h1,h2,h3⟩
    refine ⟨h3,?_,?_,?_⟩
    · rw [← cubic_frame_inverse_first a b c s1 x0 x1]
      exact dvd_add h2 (dvd_mul_of_dvd_right h3 _)
    · rw [← cubic_frame_inverse_second a b c s1 s2 x0 x1 x2]
      exact dvd_add (dvd_add h1 (dvd_mul_of_dvd_right h2 _))
        (dvd_mul_of_dvd_right h3 _)
    · rw [← cubic_frame_inverse_third a b c s1 s2 s3 x0 x1 x2 x3]
      exact dvd_add (dvd_add (dvd_add h0 (dvd_mul_of_dvd_right h1 _))
        (dvd_mul_of_dvd_right h2 _)) (dvd_mul_of_dvd_right h3 _)
  · rintro ⟨h0,h1,h2,h3⟩
    refine ⟨?_,?_,?_,h0⟩
    · unfold cubicFrame0
      have ha : d ∣ -a*b*c*x0 := dvd_mul_of_dvd_right h0 _
      have hb : d ∣ a*b*(s1*x1) := dvd_mul_of_dvd_right h1 _
      have hc : d ∣ a*(s2*x2) := dvd_mul_of_dvd_right h2 _
      simpa only [mul_assoc] using dvd_add (dvd_sub (dvd_add ha hb) hc) h3
    · unfold cubicFrame1
      have ha : d ∣ (a*b+a*c+b*c)*x0 := dvd_mul_of_dvd_right h0 _
      have hb : d ∣ (a+b)*(s1*x1) := dvd_mul_of_dvd_right h1 _
      simpa only [mul_assoc] using dvd_add (dvd_sub ha hb) h2
    · unfold cubicFrame2
      exact dvd_add (dvd_mul_of_dvd_right h0 _) h1

theorem cubic_frame_coprime_divisibility (a b c s1 s2 s3 x0 x1 x2 x3 d : ℤ)
    (h1 : IsCoprime d s1) (h2 : IsCoprime d s2) (h3 : IsCoprime d s3) :
    ((d ∣ cubicFrame0 a b c s1 s2 s3 x0 x1 x2 x3) ∧
      (d ∣ cubicFrame1 a b c s1 s2 x0 x1 x2) ∧
      (d ∣ cubicFrame2 a b c s1 x0 x1) ∧ (d ∣ x0)) ↔
      ((d ∣ x0) ∧ (d ∣ x1) ∧ (d ∣ x2) ∧ (d ∣ x3)) := by
  rw [cubic_frame_divisibility_iff]
  constructor
  · rintro ⟨ha,hb,hc,hd⟩
    exact ⟨ha,h1.dvd_of_dvd_mul_left hb,h2.dvd_of_dvd_mul_left hc,
      h3.dvd_of_dvd_mul_left hd⟩
  · rintro ⟨ha,hb,hc,hd⟩
    exact ⟨ha,dvd_mul_of_dvd_right hb _,dvd_mul_of_dvd_right hc _,
      dvd_mul_of_dvd_right hd _⟩

end OddZeta
