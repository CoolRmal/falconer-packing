/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourceWavePacketMass

/-!
# The actual first-norm cost of pin-dependent packet deletion

A finite measurable choice of packets may depend on the pin. Its actual source first norm,
and consequently its actual pinned distance first norm, are bounded by the weighted sum
of individual packet first norms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- A source made from the packets deleted at a given pin. -/
def deletedPacketSum {ι : Type*} (I : Finset ι)
    (P : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  ∑ i ∈ I.filter (fun i ↦ y ∈ P i), f i

/-- The actual source first norm of a pin-dependent finite sum has its expected averaged cost. -/
theorem lintegral_enorm_deletedPacketSum_le {ι : Type*}
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) (I : Finset ι)
    (P : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hP : ∀ i ∈ I, MeasurableSet (P i))
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫⁻ y, ∫⁻ x, ‖deletedPacketSum I P f y x‖ₑ ∂volume ∂ν) ≤
      ∑ i ∈ I, ν (P i) * ∫⁻ x, ‖f i x‖ₑ := by
  have hpoint (y : EuclideanSpace ℝ (Fin 2)) :
      (∫⁻ x, ‖deletedPacketSum I P f y x‖ₑ) ≤
        ∑ i ∈ I, (P i).indicator (fun _ ↦ ∫⁻ x, ‖f i x‖ₑ) y := by
    calc
      _ ≤ ∫⁻ x, ∑ i ∈ I.filter (fun i ↦ y ∈ P i), ‖f i x‖ₑ := by
        apply lintegral_mono
        intro x
        simpa only [deletedPacketSum, sum_apply] using
          enorm_sum_le (I.filter (fun i ↦ y ∈ P i)) (fun i ↦ f i x)
      _ = ∑ i ∈ I.filter (fun i ↦ y ∈ P i), ∫⁻ x, ‖f i x‖ₑ :=
        lintegral_finsetSum _ (fun i _ ↦ (f i).continuous.measurable.enorm)
      _ = _ := by simp only [Finset.sum_filter, indicator_apply]
  calc
    _ ≤ ∫⁻ y, ∑ i ∈ I, (P i).indicator (fun _ ↦ ∫⁻ x, ‖f i x‖ₑ) y ∂ν :=
      lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_finsetSum I (fun i hi ↦ measurable_const.indicator (hP i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_indicator (hP i hi), setLIntegral_const, mul_comm]

/-- The actual pinned density of the deleted sum has the same averaged first-norm bound. -/
theorem lintegral_enorm_pinned_deletedPacketSum_le {ι : Type*}
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) (I : Finset ι)
    (P : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hP : ∀ i ∈ I, MeasurableSet (P i))
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫⁻ y, ∫⁻ t, ‖complexDistanceDensity (deletedPacketSum I P f y) y t‖ₑ ∂volume ∂ν) ≤
      ∑ i ∈ I, ν (P i) * ∫⁻ x, ‖f i x‖ₑ :=
  (lintegral_mono fun y ↦ lintegral_enorm_complexDistanceDensity_le
    (deletedPacketSum I P f y).continuous.measurable
    (deletedPacketSum I P f y).integrable y).trans
      (lintegral_enorm_deletedPacketSum_le ν I P hP f)

end FalconerPacking
