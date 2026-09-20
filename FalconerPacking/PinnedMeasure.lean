/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.FrostmanLimit
import Mathlib.MeasureTheory.Measure.Map

/-!
# Pinned distance pushforward measures

This file isolates the last measure-theoretic implication used by both analytic branches.  If the
pushforward of a nonzero measure under `x ↦ dist x y` is absolutely continuous with respect to
Lebesgue measure, then the pinned distance set at `y` has positive Lebesgue measure.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The pinned distance measure obtained by pushing `μ` forward under `x ↦ dist x y`. -/
def pinnedDistanceMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (y : EuclideanSpace ℝ (Fin 2)) : Measure ℝ :=
  μ.map fun x ↦ dist x y

/-- Distance from a fixed pin is measurable. -/
theorem measurable_dist_right (y : EuclideanSpace ℝ (Fin 2)) :
    Measurable fun x : EuclideanSpace ℝ (Fin 2) ↦ dist x y :=
  (continuous_id.dist continuous_const).measurable

/-- The pinned distance measure of the pinned distance set is at least the mass of the source
set.  This holds without assuming that the image is measurable. -/
theorem measure_le_pinnedDistanceMeasure_pinnedDistances
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (E : Set (EuclideanSpace ℝ (Fin 2))) (y : EuclideanSpace ℝ (Fin 2)) :
    μ E ≤ pinnedDistanceMeasure μ y (pinnedDistances E y) := by
  exact Measure.le_map_apply_image (measurable_dist_right y).aemeasurable E

/-- Absolute continuity of a nonzero pinned distance measure forces the pinned distance set to
have positive Lebesgue measure. -/
theorem volume_pinnedDistances_pos_of_absolutelyContinuous
    {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    {E : Set (EuclideanSpace ℝ (Fin 2))} {y : EuclideanSpace ℝ (Fin 2)}
    (hμE : 0 < μ E) (hac : pinnedDistanceMeasure μ y ≪ volume) :
    0 < volume (pinnedDistances E y) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hpush : pinnedDistanceMeasure μ y (pinnedDistances E y) = 0 := hac hzero
  exact (not_le_of_gt hμE)
    ((measure_le_pinnedDistanceMeasure_pinnedDistances μ E y).trans_eq hpush)

/-- A displayed density for the pinned pushforward is enough to obtain positive length. -/
theorem volume_pinnedDistances_pos_of_withDensity
    {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    {E : Set (EuclideanSpace ℝ (Fin 2))} {y : EuclideanSpace ℝ (Fin 2)}
    (hμE : 0 < μ E) (f : ℝ → ℝ≥0∞)
    (hdensity : pinnedDistanceMeasure μ y = volume.withDensity f) :
    0 < volume (pinnedDistances E y) := by
  apply volume_pinnedDistances_pos_of_absolutelyContinuous hμE
  rw [hdensity]
  exact withDensity_absolutelyContinuous volume f

/-- If the pinned pushforwards are absolutely continuous for almost every pin of a nonzero
probability carried by `F`, at least one pin in `F` has a positive-length distance set. -/
theorem exists_mem_volume_pinnedDistances_pos_of_ae
    {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {E F : Set (EuclideanSpace ℝ (Fin 2))}
    (hμE : 0 < μ E)
    (hνF : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Fᶜ = 0)
    (hae : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))),
      pinnedDistanceMeasure μ y ≪ volume) :
    ∃ y ∈ F, 0 < volume (pinnedDistances E y) := by
  have hmem : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))), y ∈ F := by
    rw [ae_iff]
    exact hνF
  obtain ⟨y, hyF, hyac⟩ := (hmem.and hae).exists
  exact ⟨y, hyF, volume_pinnedDistances_pos_of_absolutelyContinuous hμE hyac⟩

/-- A probability measure giving no mass to the complement of a measurable set gives that set
mass one. -/
theorem probabilityMeasure_apply_eq_one_of_compl_eq_zero
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E)
    (hμE : (μ : Measure (EuclideanSpace ℝ (Fin 2))) Eᶜ = 0) :
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) E = 1 := by
  have hcompl := measure_compl hE (measure_ne_top (μ : Measure (EuclideanSpace ℝ (Fin 2))) E)
  rw [IsProbabilityMeasure.measure_univ] at hcompl
  rw [hcompl] at hμE
  exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.mp hμE)

/-- The form used by the branch proofs: an absolutely continuous pinned pushforward of a
probability carried by `E` gives a positive-length pinned distance set. -/
theorem volume_pinnedDistances_pos_of_probabilityMeasure
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E)
    {y : EuclideanSpace ℝ (Fin 2)}
    (hμE : (μ : Measure (EuclideanSpace ℝ (Fin 2))) Eᶜ = 0)
    (hac : pinnedDistanceMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2))) y ≪ volume) :
    0 < volume (pinnedDistances E y) := by
  apply volume_pinnedDistances_pos_of_absolutelyContinuous
    (μ := (μ : Measure (EuclideanSpace ℝ (Fin 2))))
  · rw [probabilityMeasure_apply_eq_one_of_compl_eq_zero μ hE hμE]
    exact zero_lt_one
  · exact hac

end FalconerPacking
