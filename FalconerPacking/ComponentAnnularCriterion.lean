/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AnnularDecayAssembly

/-!
# Absolute continuity from actual component density estimates

Original component masses cancel their conditional normalizations. A finite global radial
moment and exponentially small discarded pin mass therefore suffice to assemble the annular
pieces, even though individual normalized moments need not be uniformly bounded.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- Actual component estimates yield pinned absolute continuity without a component-count
loss. The only density compared with the good part is the actual compact annular source. -/
theorem pinnedDistance_absolutelyContinuous_of_eventual_component_decay {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχone : ∀ᵐ x ∂μ, χ x = 1) (hχnorm : ∀ x, ‖χ x‖ ≤ 1)
    {T : ℕ} (hT : 0 < T) {L : ℝ}
    (hL : ∀ᵐ y ∂ν, ∀ x ∈ Function.support χ, dist x y ≤ L)
    (moment : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (hmoment : (∫⁻ y, moment y ∂ν) ≠ ∞)
    {A B C : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞) (hC : C ≠ ∞)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hparts : ∀ᶠ k : ℕ in atTop,
      ∃ (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
        (g : ι → EuclideanSpace ℝ (Fin 2) × ℝ → ℂ),
        (∀ i ∈ I, MeasurableSet (U i)) ∧ (∀ i ∈ I, Measurable (g i)) ∧
        (↑I : Set ι).PairwiseDisjoint U ∧
        (∀ i ∈ I, (∫⁻ p, ‖g i p‖ₑ ^ 2 ∂(normalizedRestrict ν (U i)).prod volume) ≤
          A * (2 : ℝ≥0∞) ^ (-a * k)) ∧
        (∀ i ∈ I, (∫⁻ p, ‖complexDistanceDensity
            (compactAnnularSource μ hμ χ hχ T (k + 1)) p.1 p.2 - g i p‖ₑ
            ∂(normalizedRestrict ν (U i)).prod volume) ≤
          (B * (∫⁻ y, moment y ∂normalizedRestrict ν (U i)) + C) *
            (2 : ℝ≥0∞) ^ (-(k : ℝ))) ∧
        ν (⋃ i ∈ I, U i)ᶜ ≤ (2 : ℝ≥0∞) ^ (-b * k)) :
    jointPinnedDistanceMeasure μ ν ≪ ν.prod volume ∧
      ∀ᵐ y ∂ν, pinnedDistanceMeasure μ y ≪ volume := by
  let K := ENNReal.ofReal (2 * μ.real univ * ∫ x, ‖unitReproducingKernel x‖)
  have htotal : B * (∫⁻ y, moment y ∂ν) + C ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hB hmoment, hC⟩
  obtain ⟨D, ε, hD, hε, hdecay⟩ :=
    exists_common_annular_decay hA htotal (show K ≠ ∞ from ENNReal.ofReal_ne_top) ha hb
  apply pinnedDistance_absolutelyContinuous_of_eventual_annular_good_parts
    μ ν hμ χ hχ hχone hχnorm hT hL hD hε
  rw [← map_add_atTop_eq_nat 1]
  change ∀ᶠ k : ℕ in atTop, _
  filter_upwards [hparts] with k hk
  obtain ⟨I, U, g, hU, hg, hdis, hgood, hbad, hrem⟩ := hk
  obtain ⟨G, hG, hGa, hGb⟩ := exists_annular_good_part_of_uniform_component_bounds
    μ ν hμ χ hχ hχnorm T (k + 1) I U g hU hg hdis moment
    (A * (2 : ℝ≥0∞) ^ (-a * k)) (B * (2 : ℝ≥0∞) ^ (-(k : ℝ)))
    (C * (2 : ℝ≥0∞) ^ (-(k : ℝ))) ((2 : ℝ≥0∞) ^ (-b * k)) hgood
    (fun i hi ↦ (hbad i hi).trans_eq (by ring)) hrem
  refine ⟨G, hG, hGa.trans (hdecay k).1, ?_⟩
  apply hGb.trans
  convert (hdecay k).2 using 1 <;> first | rfl | ring

end FalconerPacking
