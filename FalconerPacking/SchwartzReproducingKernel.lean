/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.WeightedConvolutionEmbedding
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Actual Schwartz reproducing kernels

The inverse Fourier transform of a cutoff reproduces a Schwartz function when the
cutoff equals one on its Fourier support. A fixed compact smooth cutoff is constructed
explicitly; neither reproduction nor decay is assumed.
-/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal Convolution

namespace FalconerPacking

/-- An inverse Fourier cutoff reproduces the functions covered by its unit region. -/
theorem schwartz_convolution_fourierInv_cutoff
    (f χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : ∀ ξ ∈ Function.support
      (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ), χ ξ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (𝓕⁻ χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) x = f x := by
  have hfourier : 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f (𝓕⁻ χ)) =
      𝓕 f := by
    rw [SchwartzMap.fourier_convolution, fourier_fourierInv_eq]
    ext ξ
    simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply']
    by_cases hξ : (𝓕 f) ξ = 0
    · simp [hξ]
    · rw [hχ ξ hξ, mul_one]
  have hconv := congrArg
    (fun g : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ ↦ 𝓕⁻ g) hfourier
  simp only [fourierInv_fourier_eq] at hconv
  rw [← SchwartzMap.convolution_apply, hconv]

/-- A fixed smooth bump equal to one on the ball of radius two and zero beyond radius three. -/
def unitFrequencyBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) :=
  ⟨2, 3, by norm_num, by norm_num⟩

/-- The fixed complex Fourier cutoff as an actual Schwartz function. -/
def unitFrequencyCutoff : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (unitFrequencyBump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp unitFrequencyBump.contDiff)

/-- The cutoff is one throughout the unit coordinate square. -/
theorem unitFrequencyCutoff_eq_one {ξ : EuclideanSpace ℝ (Fin 2)}
    (hξ : ∀ i, |ξ i| ≤ 1) : unitFrequencyCutoff ξ = 1 := by
  have hnorm : ‖ξ‖ ≤ 2 := by
    have hs := EuclideanSpace.real_norm_sq_eq ξ
    simp only [Fin.sum_univ_two] at hs
    have h₀ := abs_le.mp (hξ 0)
    have h₁ := abs_le.mp (hξ 1)
    have h₀sq : ξ 0 ^ 2 ≤ 1 := by nlinarith
    have h₁sq : ξ 1 ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg ξ]
  change (unitFrequencyBump ξ : ℂ) = 1
  rw [unitFrequencyBump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right, unitFrequencyBump] using hnorm)]
  norm_num

/-- The cutoff has genuinely bounded Fourier-side support. -/
theorem unitFrequencyCutoff_eq_zero {ξ : EuclideanSpace ℝ (Fin 2)}
    (hξ : 3 ≤ ‖ξ‖) : unitFrequencyCutoff ξ = 0 := by
  change (unitFrequencyBump ξ : ℂ) = 0
  rw [unitFrequencyBump.zero_of_le_dist (by
    simpa only [dist_zero_right, unitFrequencyBump] using hξ)]
  norm_num

/-- A specific Schwartz reproducing kernel for the unit Fourier square. -/
def unitReproducingKernel : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  𝓕⁻ unitFrequencyCutoff

/-- The constructed kernel reproduces every Schwartz function with the stated Fourier support. -/
theorem unitReproducingKernel_reproduces
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hf : ∀ ξ ∈ Function.support
      (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ), ∀ i, |ξ i| ≤ 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ] unitReproducingKernel) x = f x :=
  schwartz_convolution_fourierInv_cutoff f unitFrequencyCutoff
    (fun ξ hξ ↦ unitFrequencyCutoff_eq_one (hf ξ hξ)) x

end FalconerPacking
