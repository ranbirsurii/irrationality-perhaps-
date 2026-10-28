import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

namespace OddZeta

def integralPairing {n : ℕ} (f v : Fin n → ℤ) : ℤ :=
  ∑ i, f i * v i

def integralKernelProjection {n : ℕ} (ell u v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => v i - u i * integralPairing ell v

def projectedIntegralRow {n : ℕ} (ell u f : Fin n → ℤ) : Fin n → ℤ :=
  fun i => f i - integralPairing f u * ell i

theorem pairing_projection {n : ℕ} (ell u f v : Fin n → ℤ) :
    integralPairing f (integralKernelProjection ell u v) =
      integralPairing f v - integralPairing f u * integralPairing ell v := by
  simp only [integralPairing, integralKernelProjection, mul_sub,
    Finset.sum_sub_distrib, ← mul_assoc, Finset.sum_mul]

theorem pairing_projected_row {n : ℕ} (ell u f v : Fin n → ℤ) :
    integralPairing (projectedIntegralRow ell u f) v =
      integralPairing f v - integralPairing f u * integralPairing ell v := by
  simp only [integralPairing, projectedIntegralRow, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

theorem integralKernelProjection_mem {n : ℕ} (ell u v : Fin n → ℤ)
    (hu : integralPairing ell u = 1) :
    integralPairing ell (integralKernelProjection ell u v) = 0 := by
  rw [pairing_projection, hu]
  ring

theorem integralKernelProjection_eq_self {n : ℕ} (ell u v : Fin n → ℤ)
    (hv : integralPairing ell v = 0) : integralKernelProjection ell u v = v := by
  funext i
  simp [integralKernelProjection, hv]

theorem integralKernelProjection_idempotent {n : ℕ} (ell u v : Fin n → ℤ)
    (hu : integralPairing ell u = 1) :
    integralKernelProjection ell u (integralKernelProjection ell u v) =
      integralKernelProjection ell u v :=
  integralKernelProjection_eq_self ell u _ (integralKernelProjection_mem ell u v hu)

theorem projected_rows_dvd_iff_kernel {n m : ℕ}
    (ell u : Fin n → ℤ) (F : Fin m → Fin n → ℤ) (c : ℤ)
    (hu : integralPairing ell u = 1) :
    (∀ a j, c ∣ projectedIntegralRow ell u (F a) j) ↔
      ∀ v : Fin n → ℤ, integralPairing ell v = 0 →
        ∀ a, c ∣ integralPairing (F a) v := by
  constructor
  · intro hc v hv a
    have heq : integralPairing (projectedIntegralRow ell u (F a)) v =
        integralPairing (F a) v := by
      rw [pairing_projected_row, hv]
      ring
    rw [← heq]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left (hc a j) _)
  · intro hc a j
    let e : Fin n → ℤ := fun i => if i = j then 1 else 0
    have he (f : Fin n → ℤ) : integralPairing f e = f j := by
      simp [integralPairing, e]
    have hd := hc (integralKernelProjection ell u e)
      (integralKernelProjection_mem ell u e hu) a
    rw [pairing_projection, he, he] at hd
    exact hd

noncomputable def projectedRowsContent {n m : ℕ}
    (ell u : Fin n → ℤ) (F : Fin m → Fin n → ℤ) : ℤ :=
  Finset.univ.gcd (fun aj : Fin m × Fin n =>
    projectedIntegralRow ell u (F aj.1) aj.2)

theorem dvd_projectedRowsContent_iff {n m : ℕ}
    (ell u : Fin n → ℤ) (F : Fin m → Fin n → ℤ) (c : ℤ)
    (hu : integralPairing ell u = 1) :
    c ∣ projectedRowsContent ell u F ↔
      ∀ v : Fin n → ℤ, integralPairing ell v = 0 →
        ∀ a, c ∣ integralPairing (F a) v := by
  rw [← projected_rows_dvd_iff_kernel ell u F c hu]
  unfold projectedRowsContent
  constructor
  · intro hc a j
    exact dvd_trans hc (Finset.gcd_dvd (Finset.mem_univ (a, j)))
  · intro hc
    exact Finset.dvd_gcd (fun aj _ => hc aj.1 aj.2)

theorem projectedRowsContent_independent_of_section {n m : ℕ}
    (ell u v : Fin n → ℤ) (F : Fin m → Fin n → ℤ)
    (hu : integralPairing ell u = 1) (hv : integralPairing ell v = 1) :
    Associated (projectedRowsContent ell u F) (projectedRowsContent ell v F) := by
  apply associated_of_dvd_dvd
  · rw [dvd_projectedRowsContent_iff ell v F _ hv]
    exact (dvd_projectedRowsContent_iff ell u F _ hu).mp (dvd_refl _)
  · rw [dvd_projectedRowsContent_iff ell u F _ hu]
    exact (dvd_projectedRowsContent_iff ell v F _ hv).mp (dvd_refl _)

end OddZeta
