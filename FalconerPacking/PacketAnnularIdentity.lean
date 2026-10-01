/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InitialPacketDecomposition
import FalconerPacking.CompactAnnularReconstruction

/-!
# Identifying the actual packet sum with the compact annular source

The real spatial cutoff used by the packets is postcomposed with the standard inclusion
into the complex numbers. With this same cutoff, the finite packet sum is exactly the
annular source appearing in the reconstruction theorem.
-/

noncomputable section

open MeasureTheory Set Classical SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- Real-to-complex postcomposition preserves compact support. -/
theorem hasCompactSupport_complex_source_cutoff
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ) :
    HasCompactSupport (χ.postcompCLM Complex.ofRealCLM) :=
  hχ.comp_left Complex.ofReal_zero

/-- All actual dyadic packets sum to the very same compact annular source used in the limit. -/
theorem sum_dyadic_sourceWavePacket_eq_compactAnnularSource
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (T n N : ℕ) (hN : 0 < N) {w : ℝ} (hw : 0 < w) :
    (∑ j ∈ Finset.range N, ∑ k ∈ sourceWavePacketIndices χ hχ w,
      sourceWavePacket μ hμ (𝓕 (dyadicAnnularKernel T n))
        (hasCompactSupport_fourier_dyadicAnnularKernel T n)
        (fourier_dyadicAnnularKernel_eventually_zero T n) χ hχ N hN w j k) =
      compactAnnularSource μ hμ (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complex_source_cutoff χ hχ) T (n + 1) := by
  ext x
  simp only [sum_apply]
  rw [sum_sourceWavePacket_eq μ hμ _ _ _ χ hχ N hN hw,
    FourierTransform.fourierInv_fourier_eq]
  rfl

/-- The circle integrand of a Schwartz source is integrable for every pin and radius. -/
theorem integrable_schwartz_pinned_circle
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Integrable (fun θ ↦ f (r • angularDirection θ + y)) radialAngularMeasure := by
  apply Integrable.of_bound (by fun_prop) (SchwartzMap.seminorm ℝ 0 0 f)
  exact ae_of_all _ fun θ ↦ SchwartzMap.norm_le_seminorm ℝ f _

/-- The actual distance-density formula is additive on Schwartz sources. -/
theorem complexDistanceDensity_add_schwartz
    (f g : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    complexDistanceDensity (f + g : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) y r =
      complexDistanceDensity f y r + complexDistanceDensity g y r := by
  unfold complexDistanceDensity pinnedCircularAverage circularAverage
  by_cases hr : 0 < r
  · simp only [hr, ↓reduceIte, add_apply]
    rw [integral_add (integrable_schwartz_pinned_circle f y r)
      (integrable_schwartz_pinned_circle g y r), smul_add, mul_add]
  · simp [hr]

/-- An exact retained-plus-deleted source identity gives its exact density remainder. -/
theorem complexDistanceDensity_sub_eq_of_source_add
    (f g h : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hadd : f + g = h)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    complexDistanceDensity h y r - complexDistanceDensity f y r =
      complexDistanceDensity g y r := by
  rw [← hadd, complexDistanceDensity_add_schwartz]
  ring

/-- The explicit real source cutoff has modulus at most one. -/
theorem abs_sourceBallCutoff_le_one (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 2)) : |sourceBallCutoff R hR x| ≤ 1 := by
  rw [sourceBallCutoff_apply, abs_of_nonneg (sourceBallBump R hR).nonneg]
  exact (sourceBallBump R hR).le_one

/-- A unit neighborhood of a bounded source lies in the unit region of the fixed cutoff. -/
theorem sourceBallCutoff_one_near_measure
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) {M : ℝ} (hM : 0 ≤ M)
    (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M) :
    ∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < 1 →
      sourceBallCutoff (M + 1) (by positivity) x = 1 := by
  filter_upwards [hμ] with z hz
  intro x hx
  apply sourceBallCutoff_eq_one
  simp only [Metric.mem_closedBall, dist_zero_right]
  have h := norm_le_norm_sub_add x z
  linarith

end FalconerPacking
