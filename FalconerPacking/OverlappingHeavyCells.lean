/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialHeavyCells
import FalconerPacking.BallOverlap

/-!
# Heavy cells with bounded overlap

Enlarged angular cells can replace a maximal operator at the finitely many relevant
scales. The deletion constant depends on their overlap, not on their number.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Bounded overlap, rather than disjointness, suffices for the heavy-cell moment estimate. -/
theorem withDensity_angularHeavyCells_le_of_overlap {α ι : Type*} [MeasurableSpace α]
    (σ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f)
    (hfinite : (∫⁻ x, f x ∂σ) ≠ ∞) (I : Finset ι) (C : ι → Set α)
    (B : ℕ) (hB : ∀ x, (I.filter (fun i ↦ x ∈ C i)).card ≤ B)
    (hC : ∀ i ∈ I, MeasurableSet (C i))
    {A : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) :
    σ.withDensity f (angularHeavyCells σ f I C (2 * A)) ≤
      2 * B * A ^ (1 - q) * ∫⁻ x, f x ^ q ∂σ := by
  let J := I.filter (fun i ↦ 2 * A * σ (C i) < ∫⁻ x in C i, f x ∂σ)
  let g := {z | A < f z}.indicator f
  have hs : MeasurableSet {x | A < f x} := measurableSet_lt measurable_const hf
  have hsum : (∑ i ∈ I, ∫⁻ x in C i, g x ∂σ) ≤ B * ∫⁻ x, g x ∂σ := by
    have h := sum_measure_le_mul_of_multiplicity (σ.withDensity g) I C
      MeasurableSet.univ hC (fun _ _ ↦ subset_univ _) B hB
    have he : (∑ i ∈ I, σ.withDensity g (C i)) = ∑ i ∈ I, ∫⁻ x in C i, g x ∂σ :=
      Finset.sum_congr rfl (fun i hi ↦ withDensity_apply _ (hC i hi))
    rw [he, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  calc
    _ ≤ ∑ i ∈ J, σ.withDensity f (C i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ J, 2 * ∫⁻ x in C i, g x ∂σ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [withDensity_apply _ (hC i (Finset.mem_filter.mp hi).1)]
      exact heavy_cell_mass_le_twice_tail σ
        (ne_top_of_le_ne_top hfinite (setLIntegral_le_lintegral _ _))
        (Finset.mem_filter.mp hi).2.le
    _ ≤ 2 * ∑ i ∈ I, ∫⁻ x in C i, g x ∂σ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_right
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ bot_le)
    _ ≤ 2 * (B * ∫⁻ x, g x ∂σ) := mul_le_mul_right hsum _
    _ = (2 * B) * σ.withDensity f {x | A < f x} := by
      rw [withDensity_apply _ hs, ← lintegral_indicator hs]
      simp only [g, mul_assoc]
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_right (withDensity_tail_le σ hf hA hAt hq) (2 * B)

/-- The actual source--pin deletion estimate for any finite bounded-overlap angular family. -/
theorem prod_radialHeavyCellPairs_le_of_overlap {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (hac : ∀ᵐ x ∂μ, ν.map (radialAngle x) ≪ radialAngularMeasure)
    (I : Finset ι) (C : ι → Set ℝ) (B : ℕ)
    (hB : ∀ θ, (I.filter (fun i ↦ θ ∈ C i)).card ≤ B)
    (hC : ∀ i ∈ I, MeasurableSet (C i))
    {A : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) :
    μ.prod ν (radialHeavyCellPairs ν I C (2 * A)) ≤
      2 * B * A ^ (1 - q) *
        ∫⁻ x, ∫⁻ θ, radialProjectionDensity ν x θ ^ q ∂radialAngularMeasure ∂μ := by
  rw [Measure.prod_apply (measurableSet_radialHeavyCellPairs ν I C (2 * A) hC)]
  calc
    _ ≤ ∫⁻ x, 2 * B * A ^ (1 - q) *
        ∫⁻ θ, radialProjectionDensity ν x θ ^ q ∂radialAngularMeasure ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hac] with x hx
      change ν (radialAngle x ⁻¹'
        angularHeavyCells radialAngularMeasure (radialProjectionDensity ν x) I C (2 * A)) ≤ _
      rw [← Measure.map_apply measurable_radialAngle.of_uncurry_left
        (measurableSet_angularHeavyCells _ _ _ _ _ hC),
        ← withDensity_radialProjectionDensity_eq ν x hx]
      exact withDensity_angularHeavyCells_le_of_overlap radialAngularMeasure
        (measurable_radialProjectionDensity ν).of_uncurry_left
        (lintegral_radialProjectionDensity_ne_top ν x) I C B hB hC hA hAt hq
    _ = _ := lintegral_const_mul _ (measurable_radialProjectionMoment ν q)

end FalconerPacking
