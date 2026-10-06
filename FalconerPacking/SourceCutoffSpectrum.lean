/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourcePacketFrequency
public import FalconerPacking.SourceCutoffError
public import Mathlib.Analysis.Fourier.Inversion

/-!
# The original source spectrum after removing the spatial cutoff

The Fourier transform of the actual convolved source is exactly the cap multiplier times
its characteristic function. The cutoff error therefore compares the actual packet sum
with the original common source spectrum, at every frequency.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped FourierTransform ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The actual convolved source is the inverse Fourier transform of its source spectrum. -/
theorem schwartzMeasureDensity_fourierInv_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    schwartzMeasureDensity μ (𝓕⁻ ψ) = 𝓕⁻ (sourcePacketSpectrum μ ψ) := by
  funext x
  rw [schwartzMeasureDensity, integral_inverseFourier_source_eq, Real.fourierInv_eq']
  simp only [smul_eq_mul]

/-- Fourier inversion identifies the actual source convolution with the original spectrum. -/
theorem fourier_schwartzMeasureDensity_eq_sourcePacketSpectrum
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    𝓕 (schwartzMeasureDensity μ (𝓕⁻ ψ)) = sourcePacketSpectrum μ ψ := by
  have hi : Integrable (𝓕⁻ (sourcePacketSpectrum μ ψ)) := by
    rw [← schwartzMeasureDensity_fourierInv_eq]
    exact integrable_schwartzMeasureDensity μ (𝓕⁻ ψ)
  have hf : Integrable (𝓕 (sourcePacketSpectrum μ ψ)) := by
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hi.comp_neg
  rw [schwartzMeasureDensity_fourierInv_eq]
  exact (continuous_sourcePacketSpectrum μ ψ).fourier_fourierInv_eq
    (integrable_sourcePacketSpectrum μ ψ) hf

/-- Multiplication by a bounded continuous real cutoff preserves actual source integrability. -/
theorem integrable_cutoff_schwartzMeasureDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hχ : Continuous χ) (hχone : ∀ x, |χ x| ≤ 1) :
    Integrable (fun x ↦ χ x • schwartzMeasureDensity μ K x) := by
  apply (integrable_schwartzMeasureDensity μ K).norm.mono'
    (hχ.aestronglyMeasurable.smul (integrable_schwartzMeasureDensity μ K).aestronglyMeasurable)
  apply ae_of_all
  intro x
  change ‖χ x • schwartzMeasureDensity μ K x‖ ≤ ‖schwartzMeasureDensity μ K x‖
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hχone x) (norm_nonneg _)).trans_eq (one_mul _)

/-- The difference from the original common spectrum is the Fourier transform of the
literal cutoff error. -/
theorem sourcePacketSpectrum_sub_fourier_cutoff_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hχ : Continuous χ) (hχone : ∀ x, |χ x| ≤ 1)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    sourcePacketSpectrum μ ψ ξ -
      (𝓕 (fun x ↦ χ x • schwartzMeasureDensity μ (𝓕⁻ ψ) x)) ξ =
      (𝓕 (fun x ↦ (1 - χ x) • schwartzMeasureDensity μ (𝓕⁻ ψ) x)) ξ := by
  rw [← fourier_schwartzMeasureDensity_eq_sourcePacketSpectrum]
  simp only [Real.fourier_eq, sub_smul, one_smul, smul_sub]
  rw [integral_sub]
  · exact (Real.fourierIntegral_convergent_iff ξ).2
      (integrable_schwartzMeasureDensity μ (𝓕⁻ ψ))
  · exact (Real.fourierIntegral_convergent_iff ξ).2
      (integrable_cutoff_schwartzMeasureDensity μ (𝓕⁻ ψ) χ hχ hχone)

/-- A pointwise comparison with the original source spectrum, with an actual kernel-tail
bound and no assumed Fourier support for the spatially cut off source. -/
theorem enorm_sourcePacketSpectrum_sub_fourier_cutoff_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hχ : Continuous χ) (hχone : ∀ x, |χ x| ≤ 1)
    (δ : ℝ) (hnear : ∀ᵐ y ∂μ, ∀ x, ‖x - y‖ < δ → χ x = 1)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖sourcePacketSpectrum μ ψ ξ -
      (𝓕 (fun x ↦ χ x • schwartzMeasureDensity μ (𝓕⁻ ψ) x)) ξ‖ₑ ≤
      2 * (∫⁻ z in {z | δ ≤ ‖z‖}, ‖(𝓕⁻ ψ) z‖ₑ) * μ univ := by
  rw [sourcePacketSpectrum_sub_fourier_cutoff_eq μ ψ χ hχ hχone]
  exact enorm_fourier_source_cutoff_error_le μ (𝓕⁻ ψ) χ hχ hχone δ hnear ξ

end FalconerPacking
