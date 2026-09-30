/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib.MeasureTheory.Integral.Average

/-!
# Choosing centers with controlled angular moments

One family of centers can be chosen in a prescribed set of full measure. At every finite
disjoint level, its mass-weighted moments are bounded by the global moment integral.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- A positive-mass cell contains a point in any prescribed full-measure set whose moment is
at most the cell average. The bound is written without division. -/
theorem exists_mem_mul_moment_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {Q G : Set α} {M : α → ℝ≥0∞}
    (hQ : 0 < μ Q) (hQt : μ Q ≠ ∞) (hG : μ Gᶜ = 0)
    (hM : AEMeasurable M (μ.restrict Q)) :
    ∃ x ∈ Q ∩ G, μ Q * M x ≤ ∫⁻ z in Q, M z ∂μ := by
  have hpos := measure_le_setLAverage_pos hQ.ne' hQt hM
  rw [← measure_sdiff_null hG] at hpos
  obtain ⟨x, hx, hxG⟩ := nonempty_of_measure_ne_zero hpos.ne'
  refine ⟨x, ⟨hx.1, by simpa only [mem_compl_iff, not_not] using hxG⟩, ?_⟩
  rw [setLAverage_eq] at hx
  have hbound := (ENNReal.le_div_iff_mul_le (Or.inl hQ.ne') (Or.inl hQt)).1 hx.2
  rwa [mul_comm] at hbound

/-- The chosen centers at any finite disjoint level have bounded mass-weighted moments. -/
theorem sum_mul_moment_le_lintegral {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (Q : ι → Set α) (c : ι → α) (M : α → ℝ≥0∞) (I : Finset ι)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hdisj : Set.PairwiseDisjoint (↑I) Q)
    (hc : ∀ i ∈ I, μ (Q i) * M (c i) ≤ ∫⁻ z in Q i, M z ∂μ) :
    ∑ i ∈ I, μ (Q i) * M (c i) ≤ ∫⁻ z, M z ∂μ := by
  calc
    ∑ i ∈ I, μ (Q i) * M (c i) ≤ ∑ i ∈ I, ∫⁻ z in Q i, M z ∂μ :=
      Finset.sum_le_sum hc
    _ = ∫⁻ z in ⋃ i ∈ I, Q i, M z ∂μ :=
      (lintegral_biUnion_finset hdisj hQ M).symm
    _ ≤ ∫⁻ z, M z ∂μ := setLIntegral_le_lintegral _ _

/-- A single center selection works for every positive-mass cell in an arbitrary indexed
family. No compatibility between different levels needs to be assumed. -/
theorem exists_moment_centers {α ι : Type*} [MeasurableSpace α] [Nonempty α]
    (μ : Measure α) [IsFiniteMeasure μ] (Q : ι → Set α) {G : Set α}
    {M : α → ℝ≥0∞} (hG : μ Gᶜ = 0) (hM : AEMeasurable M μ) :
    ∃ c : ι → α, ∀ i, 0 < μ (Q i) →
      c i ∈ Q i ∩ G ∧ μ (Q i) * M (c i) ≤ ∫⁻ z in Q i, M z ∂μ := by
  classical
  have hex (i : ι) : ∃ x : α, 0 < μ (Q i) →
      x ∈ Q i ∩ G ∧ μ (Q i) * M x ≤ ∫⁻ z in Q i, M z ∂μ := by
    by_cases hi : 0 < μ (Q i)
    · obtain ⟨x, hx, hbound⟩ := exists_mem_mul_moment_le μ hi (measure_ne_top _ _) hG
        hM.restrict
      exact ⟨x, fun _ ↦ ⟨hx, hbound⟩⟩
    · exact ⟨Classical.arbitrary α, fun h ↦ (hi h).elim⟩
  choose c hc using hex
  exact ⟨c, hc⟩

end FalconerPacking
