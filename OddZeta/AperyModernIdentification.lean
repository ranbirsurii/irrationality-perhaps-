import OddZeta.OddHankelArithmetic

namespace OddZeta

theorem aperyGKS_operator_expansion {R : Type*} [CommRing R]
    (t j0 j1 j2 j3 : R) :
    j3 - t * (34 * j3 + 51 * j2 + 27 * j1 + 5 * j0) +
      t ^ 2 * (j3 + 3 * j2 + 3 * j1 + j0) =
      (t ^ 2 - 34 * t + 1) * j3 + 3 * t * (t - 17) * j2 +
        3 * t * (t - 9) * j1 + t * (t - 5) * j0 := by
  ring

def modernAperyStep {R : Type*} [Field R] (n : ℕ) (previous current : R) : R :=
  ((2 * (n : R) + 3) *
      (17 * ((n : R) + 1) ^ 2 + 17 * ((n : R) + 1) + 5) * current -
    ((n : R) + 1) ^ 3 * previous) / ((n : R) + 2) ^ 3

theorem modernAperyStep_linear {R : Type*} [Field R]
    (n : ℕ) (a0 a1 b0 b1 c d : R) :
    modernAperyStep n (c * a0 + d * b0) (c * a1 + d * b1) =
      c * modernAperyStep n a0 a1 + d * modernAperyStep n b0 b1 := by
  unfold modernAperyStep
  ring

theorem modernApery_recurrence_unique {R : Type*} [Field R]
    (f g : ℕ → R) (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hf : ∀ n, f (n + 2) = modernAperyStep n (f n) (f (n + 1)))
    (hg : ∀ n, g (n + 2) = modernAperyStep n (g n) (g (n + 1))) : f = g := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      cases n with
      | zero => exact h1
      | succ n =>
        change f (n + 2) = g (n + 2)
        rw [hf n, hg n, ih n (by omega), ih (n + 1) (by omega)]

theorem aperyV12_period_identification_of_recurrences {R : Type*} [Field R]
    (a b v : ℕ → R) (z : R)
    (ha0 : a 0 = 1) (ha1 : a 1 = 5) (hb0 : b 0 = 0) (hb1 : b 1 = 12)
    (hv0 : v 0 = 2 * z) (hv1 : v 1 = 10 * z - 12)
    (ha : ∀ n, a (n + 2) = modernAperyStep n (a n) (a (n + 1)))
    (hb : ∀ n, b (n + 2) = modernAperyStep n (b n) (b (n + 1)))
    (hv : ∀ n, v (n + 2) = modernAperyStep n (v n) (v (n + 1))) :
    ∀ n, v n = 2 * a n * z - b n := by
  have heq : v = fun n => 2 * a n * z - b n := by
    apply modernApery_recurrence_unique v (fun n => 2 * a n * z - b n)
    · simpa [ha0, hb0] using hv0
    · rw [ha1, hb1, hv1]
      ring
    · exact hv
    · intro n
      rw [ha n, hb n]
      have h := modernAperyStep_linear n (a n) (a (n + 1)) (b n) (b (n + 1))
        (2 * z) (-1)
      convert h.symm using 1 <;> ring
  exact fun n => congrFun heq n

end OddZeta
