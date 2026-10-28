import OddZeta.SymmetricPadePeriods
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OddZeta

theorem rational_lower_period_annihilator (d : ℕ)
    (A : Fin d → Fin (d + 1) → ℚ) :
    ∃ w : Fin (d + 1) → ℚ, (∃ i, w i ≠ 0) ∧ ∀ k, ∑ i, w i * A k i = 0 := by
  let f : (Fin (d + 1) → ℚ) →ₗ[ℚ] (Fin d → ℚ) :=
    { toFun := fun w k => ∑ i, w i * A k i
      map_add' := by
        intro u v
        funext k
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        funext k
        simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker f ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨w, hw, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨w, ?_, ?_⟩
  · by_contra hn
    apply hne
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  · intro k
    exact congrFun (LinearMap.mem_ker.mp hw) k

def padeWeightMass {ι : Type*} [Fintype ι] (w : ι → ℚ) : ℚ := ∑ i, |w i|

def normalizedPadeWeight {ι : Type*} [Fintype ι] (w : ι → ℚ) (i : ι) : ℚ :=
  w i / padeWeightMass w

theorem padeWeightMass_pos {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (hw : ∃ i, w i ≠ 0) : 0 < padeWeightMass w := by
  classical
  obtain ⟨i, hi⟩ := hw
  apply Finset.sum_pos'
  · intro j _
    exact abs_nonneg _
  · exact ⟨i, Finset.mem_univ i, abs_pos.mpr hi⟩

theorem normalizedPadeWeight_l1 {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (hw : ∃ i, w i ≠ 0) : ∑ i, |normalizedPadeWeight w i| = 1 := by
  have hm := padeWeightMass_pos w hw
  simp_rw [normalizedPadeWeight, abs_div, abs_of_pos hm]
  rw [← Finset.sum_div]
  exact div_self hm.ne'

theorem normalizedPadeWeight_cancellation {ι : Type*} [Fintype ι] (w A : ι → ℚ)
    (h : ∑ i, w i * A i = 0) : ∑ i, normalizedPadeWeight w i * A i = 0 := by
  simp_rw [normalizedPadeWeight, div_mul_eq_mul_div]
  rw [← Finset.sum_div, h, zero_div]

theorem normalized_lower_period_annihilator (d : ℕ)
    (A : Fin d → Fin (d + 1) → ℚ) :
    ∃ w : Fin (d + 1) → ℚ, (∑ i, |w i| = 1) ∧ ∀ k, ∑ i, w i * A k i = 0 := by
  obtain ⟨w, hw, hA⟩ := rational_lower_period_annihilator d A
  exact ⟨normalizedPadeWeight w, normalizedPadeWeight_l1 w hw,
    fun k => normalizedPadeWeight_cancellation w (A k) (hA k)⟩

theorem normalizedPadeWeight_bound {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (f : ι → ℝ) (ε : ℝ) (hw : ∃ i, w i ≠ 0) (hf : ∀ i, |f i| ≤ ε) :
    |∑ i, (normalizedPadeWeight w i : ℝ) * f i| ≤ ε := by
  have hm : (∑ i, |(normalizedPadeWeight w i : ℝ)|) = 1 := by
    exact_mod_cast normalizedPadeWeight_l1 w hw
  calc
    _ ≤ ∑ i, |(normalizedPadeWeight w i : ℝ) * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(normalizedPadeWeight w i : ℝ)| * |f i| := by
      apply Finset.sum_congr rfl
      intro i _
      exact abs_mul _ _
    _ ≤ ∑ i, |(normalizedPadeWeight w i : ℝ)| * ε :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _))
    _ = ε := by rw [← Finset.sum_mul, hm, one_mul]

theorem normalizedPadeWeight_tendsto_zero {ι : Type*} [Fintype ι]
    (w : ℕ → ι → ℚ) (f : ℕ → ι → ℝ) (ε : ℕ → ℝ)
    (hw : ∀ n, ∃ i, w n i ≠ 0)
    (hf : ∀ᶠ n in Filter.atTop, ∀ i, |f n i| ≤ ε n)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∑ i, (normalizedPadeWeight (w n) i : ℝ) * f n i)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm' _ hε
  filter_upwards [hf] with n hn
  rw [Real.norm_eq_abs]
  exact normalizedPadeWeight_bound (w n) (f n) (ε n) (hw n) hn

end OddZeta
