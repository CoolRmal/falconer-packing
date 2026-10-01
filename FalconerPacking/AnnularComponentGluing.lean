/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AnnularRemainder

/-!
# The actual annular good part assembled from regular components

The good density is the finite sum of the component densities on their original pin sets.
Its squared second norm has the exact conditional weights. Its first-norm remainder is
bounded by the weighted component remainders plus the full annulus on discarded pins.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Gluing component good densities introduces no component-count factor in the remainder. -/
theorem lintegral_sub_componentDensitySum_le {ι : Type*}
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (g : ι → EuclideanSpace ℝ (Fin 2) × ℝ → ℂ)
    (f : EuclideanSpace ℝ (Fin 2) × ℝ → ℂ)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hg : ∀ i ∈ I, Measurable (g i))
    (hf : Measurable f) (hdis : (↑I : Set ι).PairwiseDisjoint U) :
    (∫⁻ p, ‖f p - ∑ i ∈ I, (U i ×ˢ univ).indicator (g i) p‖ₑ ∂ν.prod volume) ≤
      (∑ i ∈ I, ν (U i) * ∫⁻ p, ‖f p - g i p‖ₑ
        ∂(normalizedRestrict ν (U i)).prod volume) +
      ∫⁻ p, ‖((⋃ i ∈ I, U i)ᶜ ×ˢ univ).indicator f p‖ₑ ∂ν.prod volume := by
  have hdis' : (↑I : Set ι).PairwiseDisjoint (fun i ↦ U i ×ˢ (univ : Set ℝ)) := by
    intro i hi j hj hij
    exact Set.disjoint_left.mpr fun z hz₁ hz₂ ↦
      Set.disjoint_left.mp (hdis hi hj hij) hz₁.1 hz₂.1
  have hset : (⋃ i ∈ I, U i ×ˢ (univ : Set ℝ))ᶜ = (⋃ i ∈ I, U i)ᶜ ×ˢ univ := by
    ext p
    simp
  have hpoint (p : EuclideanSpace ℝ (Fin 2) × ℝ) :=
    sub_disjoint_indicator_sum I (fun i ↦ U i ×ˢ (univ : Set ℝ)) g f hdis' p
  simp only [hset] at hpoint
  have hsum := measurable_componentDensitySum I U (fun i p ↦ f p - g i p) hU
    (fun i hi ↦ hf.sub (hg i hi))
  calc
    _ ≤ ∫⁻ p, ‖∑ i ∈ I, (U i ×ˢ univ).indicator (fun p ↦ f p - g i p) p‖ₑ +
        ‖((⋃ i ∈ I, U i)ᶜ ×ˢ univ).indicator f p‖ₑ ∂ν.prod volume := by
      apply lintegral_mono
      intro p
      dsimp only
      rw [hpoint p]
      exact enorm_add_le _ _
    _ = (∫⁻ p, ‖∑ i ∈ I, (U i ×ˢ univ).indicator (fun p ↦ f p - g i p) p‖ₑ
        ∂ν.prod volume) +
        ∫⁻ p, ‖((⋃ i ∈ I, U i)ᶜ ×ˢ univ).indicator f p‖ₑ ∂ν.prod volume :=
      lintegral_add_left hsum.enorm _
    _ = _ := by
      congr 1
      simpa only [pow_one] using lintegral_componentDensitySum_enorm_pow ν I U
        (fun i p ↦ f p - g i p) hU (fun i hi ↦ hf.sub (hg i hi)) hdis (by norm_num : 0 < 1)

/-- The constructed global good density has precisely the needed weighted component bounds
and a discarded-mass error with a uniform source-annulus constant. -/
theorem exists_annular_good_part_of_components {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχnorm : ∀ x, ‖χ x‖ ≤ 1) (T n : ℕ)
    (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (g : ι → EuclideanSpace ℝ (Fin 2) × ℝ → ℂ)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hg : ∀ i ∈ I, Measurable (g i))
    (hdis : (↑I : Set ι).PairwiseDisjoint U) :
    let f := fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      complexDistanceDensity (compactAnnularSource μ hμ χ hχ T n) p.1 p.2
    ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → ℂ, Measurable G ∧
      (∫⁻ p, ‖G p‖ₑ ^ 2 ∂ν.prod volume) =
        ∑ i ∈ I, ν (U i) * ∫⁻ p, ‖g i p‖ₑ ^ 2
          ∂(normalizedRestrict ν (U i)).prod volume ∧
      (∫⁻ p, ‖f p - G p‖ₑ ∂ν.prod volume) ≤
        (∑ i ∈ I, ν (U i) * ∫⁻ p, ‖f p - g i p‖ₑ
          ∂(normalizedRestrict ν (U i)).prod volume) +
        ENNReal.ofReal (2 * μ.real univ * ∫ x, ‖unitReproducingKernel x‖) *
          ν (⋃ i ∈ I, U i)ᶜ := by
  dsimp only
  refine ⟨fun p ↦ ∑ i ∈ I, (U i ×ˢ univ).indicator (g i) p,
    measurable_componentDensitySum I U g hU hg,
    lintegral_componentDensitySum_enorm_pow ν I U g hU hg hdis (by norm_num), ?_⟩
  exact (lintegral_sub_componentDensitySum_le ν I U g _ hU hg
    (measurable_joint_complexDistanceDensity
      (compactAnnularSource μ hμ χ hχ T n).continuous.measurable) hdis).trans
      (add_le_add le_rfl (lintegral_annular_density_indicator_le μ ν hμ χ hχ hχnorm T n
        (I.measurableSet_biUnion hU).compl))

/-- Uniform component estimates and a discarded-mass bound give the required global norms.
The radial moment is integrated against the original pin measure before any normalization. -/
theorem exists_annular_good_part_of_uniform_component_bounds {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχnorm : ∀ x, ‖χ x‖ ≤ 1) (T n : ℕ)
    (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (g : ι → EuclideanSpace ℝ (Fin 2) × ℝ → ℂ)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (hg : ∀ i ∈ I, Measurable (g i))
    (hdis : (↑I : Set ι).PairwiseDisjoint U)
    (moment : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (a b c r : ℝ≥0∞)
    (hgood : ∀ i ∈ I, (∫⁻ p, ‖g i p‖ₑ ^ 2 ∂(normalizedRestrict ν (U i)).prod volume) ≤ a)
    (hbad : ∀ i ∈ I,
      (∫⁻ p, ‖complexDistanceDensity (compactAnnularSource μ hμ χ hχ T n) p.1 p.2 -
        g i p‖ₑ ∂(normalizedRestrict ν (U i)).prod volume) ≤
          b * (∫⁻ y, moment y ∂normalizedRestrict ν (U i)) + c)
    (hrem : ν (⋃ i ∈ I, U i)ᶜ ≤ r) :
    ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → ℂ, Measurable G ∧
      (∫⁻ p, ‖G p‖ₑ ^ 2 ∂ν.prod volume) ≤ a ∧
      (∫⁻ p, ‖complexDistanceDensity (compactAnnularSource μ hμ χ hχ T n) p.1 p.2 -
        G p‖ₑ ∂ν.prod volume) ≤
          b * (∫⁻ y, moment y ∂ν) + c +
            ENNReal.ofReal (2 * μ.real univ * ∫ x, ‖unitReproducingKernel x‖) * r := by
  obtain ⟨G, hG, hGeq, hGb⟩ := exists_annular_good_part_of_components
    μ ν hμ χ hχ hχnorm T n I U g hU hg hdis
  have hmass : ∑ i ∈ I, ν (U i) ≤ 1 := by
    rw [← measure_biUnion_finset hdis hU]
    exact prob_le_one
  refine ⟨G, hG, ?_, ?_⟩
  · rw [hGeq]
    calc
      _ ≤ ∑ i ∈ I, ν (U i) * a :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul' le_rfl (hgood i hi)
      _ = (∑ i ∈ I, ν (U i)) * a := (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * a := mul_le_mul' hmass le_rfl
      _ = a := one_mul _
  · apply hGb.trans
    apply add_le_add ?_ (mul_le_mul' le_rfl hrem)
    have hb := sum_weighted_component_deletion_le ν I U hU hdis moment b c
    simp only [measure_univ, mul_one] at hb
    exact (Finset.sum_le_sum fun i hi ↦ mul_le_mul' le_rfl (hbad i hi)).trans hb

end FalconerPacking
