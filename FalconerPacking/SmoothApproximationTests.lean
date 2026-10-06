/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SmoothProbabilityApproximation

/-!
# Smoothing tests with almost-everywhere continuity

The approximate identity also converges against bounded measurable tests that are continuous
at almost every source point. This permits angular maps with a null branch-cut set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal ContDiff Convolution Topology

namespace FalconerPacking

/-- Approximation against a bounded measurable test only requires continuity almost everywhere. -/
theorem tendsto_integral_smoothSource_of_ae_continuousAt
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)))
    (hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0))
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B)
    (hcont : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))), ContinuousAt g x) :
    Tendsto (fun n ↦ ∫ x, g x ∂(smoothSourceProbability μ (φ n) : Measure _))
      atTop (𝓝 (∫ x, g x ∂(μ : Measure _))) := by
  have hm : StronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 2) ↦ g (p.1 + p.2)) :=
    (hg.comp (measurable_fst.add measurable_snd)).stronglyMeasurable
  have hlim : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))),
      Tendsto (fun n ↦ ∫ y, g (x + y) ∂smoothBumpMeasure (φ n)) atTop (𝓝 (g x)) := by
    filter_upwards [hcont] with x hx
    simp_rw [integral_smoothBumpMeasure_add]
    exact ContDiffBump.convolution_tendsto_right hφ
      (Eventually.of_forall fun _ ↦ hg.aestronglyMeasurable)
      (Tendsto.comp hx tendsto_snd) tendsto_const_nhds
  have hb (n : ℕ) : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))),
      ‖∫ y, g (x + y) ∂smoothBumpMeasure (φ n)‖ ≤ B := by
    exact Eventually.of_forall fun x ↦ by
      simpa using norm_integral_le_of_norm_le_const
        (μ := smoothBumpMeasure (φ n)) (Eventually.of_forall fun y ↦ hB (x + y))
  have h := tendsto_integral_of_dominated_convergence (μ := (μ : Measure _)) (fun _ ↦ B)
    (fun n ↦ (hm.integral_prod_right' (ν := smoothBumpMeasure (φ n))).aestronglyMeasurable)
    (integrable_const _) hb hlim
  convert h using 1
  funext n
  change (∫ x, g x ∂((μ : Measure _) ∗ smoothBumpMeasure (φ n))) = _
  apply integral_conv
  exact (integrable_const B).mono' hg.aestronglyMeasurable (Eventually.of_forall hB)

/-- The same approximation holds jointly with any fixed finite parameter measure. -/
theorem tendsto_joint_integral_smoothSource_of_ae_continuousAt
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [IsFiniteMeasure κ]
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)))
    (hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0))
    {g : α → EuclideanSpace ℝ (Fin 2) → ℝ} (hg : Measurable (Function.uncurry g))
    {B : ℝ} (hB : ∀ z x, ‖g z x‖ ≤ B)
    (hcont : ∀ᵐ z ∂κ, ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))),
      ContinuousAt (g z) x) :
    Tendsto (fun n ↦ ∫ z, ∫ x, g z x
      ∂(smoothSourceProbability μ (φ n) : Measure _) ∂κ)
      atTop (𝓝 (∫ z, ∫ x, g z x ∂(μ : Measure _) ∂κ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ B)
  · intro n
    exact (hg.stronglyMeasurable.integral_prod_right
      (ν := (smoothSourceProbability μ (φ n) : Measure _))).aestronglyMeasurable
  · exact integrable_const B
  · intro n
    exact Eventually.of_forall fun z ↦ by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (smoothSourceProbability μ (φ n) : Measure _))
        (Eventually.of_forall fun x ↦ hB z x)
  · filter_upwards [hcont] with z hz
    exact tendsto_integral_smoothSource_of_ae_continuousAt μ φ hφ
      hg.of_uncurry_left (hB z) hz

end FalconerPacking
