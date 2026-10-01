/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.WeightedConditionalDeletion
import FalconerPacking.AnnularPinnedReconstruction

/-!
# Gluing density estimates over disjoint regular components

The assembled density uses the original measure on each component. Disjointness makes both
its first norm and its squared second norm the exact mass-weighted sum of the conditional
norms. In particular, no factor counting the regular components is introduced.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Applying a function that vanishes at zero commutes with a sum supported on disjoint sets. -/
theorem map_disjoint_indicator_sum {α ι β : Type*} [AddCommMonoid β]
    (I : Finset ι) (U : ι → Set α) (f : ι → α → ℂ) (φ : ℂ → β) (hφ : φ 0 = 0)
    (hdis : (↑I : Set ι).PairwiseDisjoint U) (x : α) :
    φ (∑ i ∈ I, (U i).indicator (f i) x) =
      ∑ i ∈ I, (U i).indicator (fun x ↦ φ (f i x)) x := by
  by_cases hmem : ∃ i ∈ I, x ∈ U i
  · obtain ⟨i, hi, hxi⟩ := hmem
    have hother (j : ι) (hj : j ∈ I) (hji : j ≠ i) : x ∉ U j := by
      exact fun hxj ↦ Set.disjoint_left.mp (hdis hj hi hji) hxj hxi
    rw [Finset.sum_eq_single i (fun j hj hji ↦ indicator_of_notMem (hother j hj hji) _)
      (fun h ↦ (h hi).elim),
      Finset.sum_eq_single i (fun j hj hji ↦ indicator_of_notMem (hother j hj hji) _)
        (fun h ↦ (h hi).elim), indicator_of_mem hxi, indicator_of_mem hxi]
  · have hnone : ∀ i ∈ I, x ∉ U i := by simpa using hmem
    simp only [Finset.sum_congr rfl (fun i hi ↦ indicator_of_notMem (hnone i hi) _),
      Finset.sum_const_zero, hφ]

/-- Mass weighting exactly undoes normalization on a pin component for any joint integral. -/
theorem measure_mul_joint_lintegral_normalizedRestrict
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    {U : Set (EuclideanSpace ℝ (Fin 2))} (_hU : MeasurableSet U)
    (f : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ≥0∞) :
    ν U * (∫⁻ p, f p ∂(normalizedRestrict ν U).prod volume) =
      ∫⁻ p in U ×ˢ univ, f p ∂ν.prod volume := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← Measure.prod_smul_left,
    measure_smul_normalizedRestrict, Measure.restrict_prod_eq_prod_univ]

/-- The assembled density is measurable whenever its finite component densities are. -/
theorem measurable_componentDensitySum {ι : Type*}
    (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (f : ι → EuclideanSpace ℝ (Fin 2) × ℝ → ℂ)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hf : ∀ i ∈ I, Measurable (f i)) :
    Measurable (fun p ↦ ∑ i ∈ I, (U i ×ˢ univ).indicator (f i) p) := by
  exact Finset.measurable_sum I fun i hi ↦ (hf i hi).indicator ((hU i hi).prod MeasurableSet.univ)

/-- Exact conditional norm gluing, for both the first norm and squared second norm. -/
theorem lintegral_componentDensitySum_enorm_pow {ι : Type*}
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (f : ι → EuclideanSpace ℝ (Fin 2) × ℝ → ℂ)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hf : ∀ i ∈ I, Measurable (f i))
    (hdis : (↑I : Set ι).PairwiseDisjoint U) {p : ℕ} (hp : 0 < p) :
    (∫⁻ z, ‖∑ i ∈ I, (U i ×ˢ univ).indicator (f i) z‖ₑ ^ p ∂ν.prod volume) =
      ∑ i ∈ I, ν (U i) *
        ∫⁻ z, ‖f i z‖ₑ ^ p ∂(normalizedRestrict ν (U i)).prod volume := by
  have hdis' : (↑I : Set ι).PairwiseDisjoint (fun i ↦ U i ×ˢ (univ : Set ℝ)) := by
    intro i hi j hj hij
    exact Set.disjoint_left.mpr fun z hz₁ hz₂ ↦
      Set.disjoint_left.mp (hdis hi hj hij) hz₁.1 hz₂.1
  have hpoint (z : EuclideanSpace ℝ (Fin 2) × ℝ) :=
    map_disjoint_indicator_sum I (fun i ↦ U i ×ˢ (univ : Set ℝ)) f
      (fun w : ℂ ↦ ‖w‖ₑ ^ p) (by simp [Nat.ne_of_gt hp]) hdis' z
  simp_rw [hpoint]
  rw [lintegral_finsetSum I (fun i hi ↦
    ((hf i hi).enorm.pow_const p).indicator ((hU i hi).prod MeasurableSet.univ))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_indicator ((hU i hi).prod MeasurableSet.univ),
    measure_mul_joint_lintegral_normalizedRestrict ν (hU i hi)]

end FalconerPacking
