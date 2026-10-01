/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SpectralCircleLinearity
import FalconerPacking.SourceCutoffSpectrum

/-!
# Initial spectral reconstruction from actual retained source packets

Good standard labels retain every spatial strip. Other labels retain only the specified
remote strips. The common source spectrum is explicitly the original cap multiplier
times the Fourier transform of the same source measure.
-/

noncomputable section

open MeasureTheory Set Function FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The common standard spectra are integrable on every frequency circle. -/
theorem integrable_sourcePacketSpectrum_circle
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (r : ℝ) :
    Integrable (sourcePacketSpectrum μ ψ) (normalizedCircleMeasure r) := by
  apply Integrable.of_bound (continuous_sourcePacketSpectrum μ ψ).aestronglyMeasurable
    (SchwartzMap.seminorm ℝ 0 0 ψ * μ.real univ)
  exact ae_of_all _ fun ξ ↦ (norm_sourcePacketSpectrum_le μ ψ ξ).trans
    (mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ ψ ξ) ENNReal.toReal_nonneg)

/-- Real-valued form of the proved pointwise cutoff-removal error. -/
theorem norm_sourcePacketSpectrum_sub_fourier_cutoff_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hχ : Continuous χ) (hχone : ∀ x, |χ x| ≤ 1)
    (δ : ℝ) (hnear : ∀ᵐ y ∂μ, ∀ x, ‖x - y‖ < δ → χ x = 1)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖sourcePacketSpectrum μ ψ ξ -
      (𝓕 (fun x ↦ χ x • schwartzMeasureDensity μ (𝓕⁻ ψ) x)) ξ‖ ≤
      2 * (∫ z in {z | δ ≤ ‖z‖}, ‖(𝓕⁻ ψ) z‖) * μ.real univ := by
  have h := enorm_sourcePacketSpectrum_sub_fourier_cutoff_le μ ψ χ hχ hχone δ hnear ξ
  rw [← ofReal_integral_norm_eq_lintegral_enorm (𝓕⁻ ψ).integrable.restrict] at h
  have hf : (2 * ENNReal.ofReal (∫ z in {z | δ ≤ ‖z‖}, ‖(𝓕⁻ ψ) z‖) * μ univ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (measure_ne_top μ univ)
  have hreal := ENNReal.toReal_mono hf h
  simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
    Measure.real]
    using hreal

/-- Summing all actual spatial packets of one standard label gives its original circle
extension up to the actual radial kernel tail of the fixed cutoff. -/
theorem norm_full_standard_packets_sub_common_spectrum_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) (N : ℕ) (hN : 0 < N) {w : ℝ} (hw : 0 < w)
    (j : ℕ) (δ : ℝ) (hnear : ∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    ‖pinnedSpectralCircleAverage
      (∑ k ∈ sourceWavePacketIndices χ hχ w,
        sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) y r -
      circleSpectralExtension r (sourcePacketSpectrum μ (smoothAngularCap ψ hψ hzero N hN j)) y‖ ≤
      2 * (∫ z in {z | δ ≤ ‖z‖}, ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖) *
        μ.real univ := by
  let f := ∑ k ∈ sourceWavePacketIndices χ hχ w,
    sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k
  have hf : (f : EuclideanSpace ℝ (Fin 2) → ℂ) = fun x ↦
      χ x • schwartzMeasureDensity μ (𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) x := by
    funext x
    simpa only [f, sum_apply, Complex.real_smul, schwartzMeasureDensity] using
      sum_sourceWavePacket_strips μ hμ ψ hψ hzero χ hχ N hN hw j x
  change ‖pinnedSpectralCircleAverage f y r - _‖ ≤ _
  rw [pinnedSpectralCircleAverage_eq_extension]
  apply norm_circleSpectralExtension_sub_le
    (integrable_schwartz_normalizedCircleMeasure (𝓕 f) r)
    (integrable_sourcePacketSpectrum_circle μ _ r) y
  refine ae_of_all _ fun ξ ↦ ?_
  rw [norm_sub_rev]
  simpa only [SchwartzMap.fourier_coe, hf] using
    norm_sourcePacketSpectrum_sub_fourier_cutoff_le μ
      (smoothAngularCap ψ hψ hzero N hN j) χ χ.continuous hχone δ hnear ξ

section RetainedPackets

variable (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
  {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
  (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
  (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
  (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
  (N : ℕ) (hN : 0 < N) (w : ℝ)

/-- The actual retained source for an initial pin cell: whole good standard labels and
only the specified remote strips of the other standard labels. -/
def initialRetainedSource (G : Finset ℕ) (remote : ℕ → Finset ℤ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (∑ j ∈ G, ∑ k ∈ sourceWavePacketIndices χ hχ w,
    sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) +
  ∑ j ∈ Finset.range N \ G, ∑ k ∈ remote j,
    sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k

/-- The original cap spectra with a whole-standard-label mask; the underlying measure and
cap functions are common to all initial pin cells. -/
def initialCommonSourceSpectrum (G : Finset ℕ) (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ∑ j ∈ G, sourcePacketSpectrum μ (smoothAngularCap ψ hψ hzero N hN j) ξ

/-- Exact finite spectral decomposition before any estimate is applied. -/
theorem initialRetainedSource_spectral_decomposition
    (G : Finset ℕ) (remote : ℕ → Finset ℤ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    pinnedSpectralCircleAverage
      (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote) y r =
      (∑ j ∈ G, pinnedSpectralCircleAverage
        (∑ k ∈ sourceWavePacketIndices χ hχ w,
          sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k :
            SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) y r) +
      ∑ j ∈ Finset.range N \ G, ∑ k ∈ remote j,
        pinnedSpectralCircleAverage
          (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) y r := by
  rw [initialRetainedSource, pinnedSpectralCircleAverage_add]
  simp_rw [pinnedSpectralCircleAverage_finsetSum]

/-- The complete reconstruction error is the sum of actual cutoff tails and actual remote
spectral averages. No auxiliary Fourier-label cutoff is applied to a spatial packet. -/
theorem norm_initialRetainedSource_sub_common_le
    (hχone : ∀ x, |χ x| ≤ 1) (hw : 0 < w)
    (G : Finset ℕ) (remote : ℕ → Finset ℤ)
    (δ : ℝ) (hnear : ∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    ‖pinnedSpectralCircleAverage
      (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote) y r -
      circleSpectralExtension r (initialCommonSourceSpectrum μ ψ hψ hzero N hN G) y‖ ≤
      (∑ j ∈ G, 2 * (∫ z in {z | δ ≤ ‖z‖},
        ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖) * μ.real univ) +
      ∑ j ∈ Finset.range N \ G, ∑ k ∈ remote j,
        ‖pinnedSpectralCircleAverage
          (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) y r‖ := by
  rw [initialRetainedSource_spectral_decomposition]
  unfold initialCommonSourceSpectrum
  rw [circleSpectralExtension_finsetSum G _ r
      (fun j _ ↦ integrable_sourcePacketSpectrum_circle μ _ r)]
  rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun j _ ↦
      norm_full_standard_packets_sub_common_spectrum_le μ hμ ψ hψ hzero χ hχ hχone
        N hN hw j δ hnear y r
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun j _ ↦ norm_sum_le _ _

end RetainedPackets

/-- Uniform initial reconstruction using the actual remote estimate and actual radial
cutoff tails. The constants are independent of all source, cap-grid, and selection data. -/
theorem exists_initial_spectral_reconstruction_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) (m : ℕ) (L : ℝ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
        (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
        (N : ℕ) (hN : 0 < N) (w γ : ℝ),
        0 < w → w ≤ 1 → (N : ℝ)⁻¹ ≤ γ → γ ≤ 1 →
        ∀ (G : Finset ℕ) (remote : ℕ → Finset ℤ) (δ : ℝ),
          (∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1) →
          ∀ y : EuclideanSpace ℝ (Fin 2), sourceCutoffRadius χ hχ + ‖y‖ ≤ L →
            (∀ j ∈ Finset.range N \ G, ∀ k ∈ remote j,
              γ + w + L * (16 * Real.pi / N) ≤
                |⟪sourceWavePacketNormal N j, y⟫ - w * k|) →
            ∀ r : ℝ, 0 < r →
              ‖pinnedSpectralCircleAverage
                (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote) y r -
                circleSpectralExtension r
                  (initialCommonSourceSpectrum μ ψ hψ hzero N hN G) y‖ ≤
                (∑ j ∈ G, 2 * (∫ z in {z | δ ≤ ‖z‖},
                  ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖) * μ.real univ) +
                ∑ j ∈ Finset.range N \ G, ∑ _k ∈ remote j,
                  (C₁ * (r * (N : ℝ)⁻¹ * γ)⁻¹ ^ m *
                    (μ.real univ * ∫ x, ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) x‖) +
                  (w * C₂ / (1 + w * r * (2 * Real.pi / N)) ^ m) * μ.real univ *
                    ∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hc⟩ :=
    exists_remote_sourceWavePacket_spectral_kernel_bound χ hχ hχone m L
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro μ _ M hμ ψ hψ hzero N hN w γ hw hw₁ hNγ hγ₁ G remote δ hnear y hy hremote r hr
  apply (norm_initialRetainedSource_sub_common_le μ hμ ψ hψ hzero χ hχ N hN w hχone hw
    G remote δ hnear y r).trans
  apply add_le_add_right
  exact Finset.sum_le_sum fun j hj ↦ Finset.sum_le_sum fun k hk ↦
    hc μ M hμ ψ hψ hzero N hN j w γ hw hw₁ hNγ hγ₁ k y hy (hremote j hj k hk) r hr

end FalconerPacking
