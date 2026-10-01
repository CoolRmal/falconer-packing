/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DisjointComponentDensities
import FalconerPacking.SourceWavePacketMass

/-!
# Discarded pin mass in the annular decomposition

The first norm of every full source annulus is uniformly bounded. Assigning the full density
to the discarded pin set therefore costs only the original discarded mass, independent of
the frequency and of the regular partition.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- The full source annulus on an arbitrary discarded pin set costs only its measure. -/
theorem lintegral_annular_density_indicator_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχnorm : ∀ x, ‖χ x‖ ≤ 1) (T n : ℕ)
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : MeasurableSet U) :
    (∫⁻ p, ‖(U ×ˢ univ).indicator
      (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦ complexDistanceDensity
        (compactAnnularSource μ hμ χ hχ T n) p.1 p.2) p‖ₑ ∂ν.prod volume) ≤
      ENNReal.ofReal (2 * μ.real univ * ∫ x, ‖unitReproducingKernel x‖) * ν U := by
  let f := compactAnnularSource μ hμ χ hχ T n
  have hfull := (measurable_joint_complexDistanceDensity f.continuous.measurable).enorm
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator (hU.prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ,
    lintegral_prod _ hfull.aemeasurable]
  have hsource : (∫⁻ x, ‖f x‖ₑ) ≤
      ENNReal.ofReal (2 * μ.real univ * ∫ x, ‖unitReproducingKernel x‖) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm f.integrable]
    exact ENNReal.ofReal_le_ofReal
      (integral_norm_compactAnnularSource_le μ hμ χ hχ hχnorm T n)
  calc
    _ ≤ ∫⁻ _y, ENNReal.ofReal (2 * μ.real univ * ∫ x, ‖unitReproducingKernel x‖)
        ∂ν.restrict U :=
      lintegral_mono fun y ↦ (lintegral_enorm_complexDistanceDensity_le
        f.continuous.measurable f.integrable y).trans hsource
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- The remainder after gluing component good parts splits exactly into their component
remainders and the full density on the discarded pin set. -/
theorem sub_disjoint_indicator_sum {α ι : Type*}
    (I : Finset ι) (U : ι → Set α) (g : ι → α → ℂ) (f : α → ℂ)
    (hdis : (↑I : Set ι).PairwiseDisjoint U) (x : α) :
    f x - ∑ i ∈ I, (U i).indicator (g i) x =
      (∑ i ∈ I, (U i).indicator (fun x ↦ f x - g i x) x) +
        (⋃ i ∈ I, U i)ᶜ.indicator f x := by
  by_cases hmem : ∃ i ∈ I, x ∈ U i
  · obtain ⟨i, hi, hxi⟩ := hmem
    have hother (j : ι) (hj : j ∈ I) (hji : j ≠ i) : x ∉ U j :=
      fun hxj ↦ Set.disjoint_left.mp (hdis hj hi hji) hxj hxi
    have hxin : x ∈ ⋃ i ∈ I, U i := mem_iUnion₂.mpr ⟨i, hi, hxi⟩
    rw [Finset.sum_eq_single i (fun j hj hji ↦ indicator_of_notMem (hother j hj hji) _)
      (fun h ↦ (h hi).elim),
      Finset.sum_eq_single i (fun j hj hji ↦ indicator_of_notMem (hother j hj hji) _)
        (fun h ↦ (h hi).elim)]
    simp only [indicator_of_mem hxi, indicator_of_notMem (show x ∉ (⋃ i ∈ I, U i)ᶜ from fun hx ↦ hx hxin), add_zero]
  · have hnone : ∀ i ∈ I, x ∉ U i := by simpa using hmem
    have hxout : x ∈ (⋃ i ∈ I, U i)ᶜ := by
      intro hin
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hin
      exact hmem ⟨i, hi, hxi⟩
    simp only [Finset.sum_congr rfl (fun i hi ↦ indicator_of_notMem (hnone i hi) _),
      Finset.sum_const_zero, indicator_of_mem hxout, sub_zero, zero_add]

end FalconerPacking
