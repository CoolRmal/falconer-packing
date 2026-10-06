/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourceWavePackets
public import FalconerPacking.FullCirclePacketDecay
public import FalconerPacking.ComplexDistancePushforward

/-!
# Frequency representations of the constructed source packets

All exchanges of the source, frequency, and angular integrals are justified by absolute
integrability. The source enters through its actual characteristic function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The frequency amplitude of convolution with a finite source measure, in the `2π`
normalization of the inverse Fourier transform. -/
def sourcePacketSpectrum (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ψ ξ * charFun μ ((-2 * Real.pi) • ξ)

theorem continuous_sourcePacketSpectrum
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Continuous (sourcePacketSpectrum μ ψ) :=
  ψ.continuous.mul (continuous_charFun.comp (continuous_id.const_smul (-2 * Real.pi)))

theorem norm_sourcePacketSpectrum_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖sourcePacketSpectrum μ ψ ξ‖ ≤ ‖ψ ξ‖ * μ.real univ := by
  exact (norm_mul _ _).le.trans
    (mul_le_mul_of_nonneg_left (norm_charFun_le _) (norm_nonneg _))

theorem integrable_sourcePacketSpectrum
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Integrable (sourcePacketSpectrum μ ψ) :=
  (ψ.integrable.norm.mul_const (μ.real univ)).mono'
    (continuous_sourcePacketSpectrum μ ψ).aestronglyMeasurable
    (ae_of_all _ (norm_sourcePacketSpectrum_le μ ψ))

/-- Absolute integrability of the actual inverse-Fourier/source integrand. -/
theorem integrable_inverseFourier_source_prod
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      Complex.exp ((2 * Real.pi * ⟪p.2, x - p.1⟫ : ℝ) * Complex.I) * ψ p.2)
      (μ.prod volume) := by
  apply (ψ.integrable.norm.comp_snd μ).mono' (by fun_prop)
  exact ae_of_all _ fun p ↦ by simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    le_refl]

/-- Convolution with the inverse Fourier kernel has its literal frequency-integral
representation, with no distributional interpretation. -/
theorem integral_inverseFourier_source_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∫ z, (𝓕⁻ ψ) (x - z) ∂μ) =
      ∫ ξ, Complex.exp ((2 * Real.pi * ⟪ξ, x⟫ : ℝ) * Complex.I) *
        sourcePacketSpectrum μ ψ ξ := by
  simp_rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', smul_eq_mul]
  rw [integral_integral_swap (integrable_inverseFourier_source_prod μ ψ x)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [sourcePacketSpectrum, charFun_apply, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  rw [real_inner_smul_right, real_inner_comm ξ z]
  have he : ((2 * Real.pi * ⟪ξ, x - z⟫ : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * ⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I +
        (((-2 * Real.pi) * ⟪ξ, z⟫ : ℝ) : ℂ) * Complex.I := by
    rw [inner_sub_right]
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

/-- Exact frequency representation of each constructed source wave packet. -/
theorem sourceWavePacket_eq_frequency_integral
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (j : ℕ) (k : ℤ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k x =
      (smoothStripPacket χ w (sourceWavePacketNormal N j) k x : ℂ) *
        ∫ ξ, Complex.exp ((2 * Real.pi * ⟪ξ, x⟫ : ℝ) * Complex.I) *
          sourcePacketSpectrum μ (smoothAngularCap ψ hψ hzero N hN j) ξ := by
  rw [sourceWavePacket_apply, integral_inverseFourier_source_eq]

/-- An integrable angular amplitude permits absolute Fubini with the full source spectrum. -/
theorem integrable_circle_sourceSpectrum_prod
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {a : ℝ → ℂ} (ha : Integrable a radialAngularMeasure)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      a p.1 * (Complex.exp ((2 * Real.pi * ⟪p.2, y - r • angularDirection p.1⟫ : ℝ) *
        Complex.I) * sourcePacketSpectrum μ ψ p.2))
      (radialAngularMeasure.prod volume) := by
  apply (ha.norm.mul_prod (integrable_sourcePacketSpectrum μ ψ).norm).mono'
  · exact ha.aestronglyMeasurable.comp_fst.mul
      ((by fun_prop : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
        Complex.exp ((2 * Real.pi * ⟪p.2, y - r • angularDirection p.1⟫ : ℝ) *
          Complex.I))).aestronglyMeasurable.mul
        (continuous_sourcePacketSpectrum μ ψ).aestronglyMeasurable.comp_snd)
  · exact ae_of_all _ fun p ↦ by
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- The complete circle/source convolution equals a frequency integral of the oscillatory
circle integral. This is an identity of ordinary absolutely convergent integrals. -/
theorem integral_circle_inverseFourier_source_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {a : ℝ → ℂ} (ha : Integrable a radialAngularMeasure)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    (∫ θ, a θ * (∫ z, (𝓕⁻ ψ) (y - r • angularDirection θ - z) ∂μ)
      ∂radialAngularMeasure) =
    ∫ ξ, (Complex.exp ((2 * Real.pi * ⟪ξ, y⟫ : ℝ) * Complex.I) *
      sourcePacketSpectrum μ ψ ξ) *
        ∫ θ, Complex.exp ((-2 * Real.pi * r * ⟪ξ, angularDirection θ⟫ : ℝ) *
          Complex.I) * a θ ∂radialAngularMeasure := by
  simp_rw [integral_inverseFourier_source_eq μ ψ, ← integral_const_mul]
  rw [integral_integral_swap (integrable_circle_sourceSpectrum_prod μ ψ ha y r)]
  apply integral_congr_ae
  filter_upwards with ξ
  apply integral_congr_ae
  filter_upwards with θ
  have he : ((2 * Real.pi * ⟪ξ, y - r • angularDirection θ⟫ : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * ⟪ξ, y⟫ : ℝ) : ℂ) * Complex.I +
        ((-2 * Real.pi * r * ⟪ξ, angularDirection θ⟫ : ℝ) : ℂ) * Complex.I := by
    rw [inner_sub_right, real_inner_smul_right]
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

theorem integrable_circularPacketAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (k : ℤ) (r : ℝ) :
    Integrable (fun θ ↦ (circularPacketAmplitude χ w e y k r θ : ℂ))
      radialAngularMeasure := by
  apply Integrable.of_bound
    (Complex.continuous_ofReal.comp
      (contDiff_circularPacketAmplitude χ w e y k r).continuous).aestronglyMeasurable
    (SchwartzMap.seminorm ℝ 0 0 χ)
  apply ae_of_all
  intro θ
  simp only [Function.comp_apply, Complex.norm_real, circularPacketAmplitude,
    smoothStripPacket, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (smoothStripWeight_nonneg w k _)]
  exact (mul_le_mul_of_nonneg_left (smoothStripWeight_le_one w k _) (abs_nonneg _)).trans
    (by simpa using SchwartzMap.norm_le_seminorm ℝ χ (y - r • angularDirection θ))

/-- Actual distance-density representation of the explicitly constructed source packet. -/
theorem complexDistanceDensity_sourceWavePacket_eq_frequency
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (j : ℕ) (k : ℤ)
    (y : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    complexDistanceDensity (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) y r =
      (r : ℂ) * ∫ ξ, (Complex.exp ((2 * Real.pi * ⟪ξ, y⟫ : ℝ) * Complex.I) *
        sourcePacketSpectrum μ (smoothAngularCap ψ hψ hzero N hN j) ξ) *
          ∫ θ, Complex.exp ((-2 * Real.pi * r * ⟪ξ, angularDirection θ⟫ : ℝ) *
            Complex.I) *
            (circularPacketAmplitude χ w (sourceWavePacketNormal N j) y k r θ : ℂ)
            ∂radialAngularMeasure := by
  rw [complexDistanceDensity_eq_circle_integral _ _ hr]
  congr 1
  simpa only [sourceWavePacket_apply, circularPacketAmplitude] using
    integral_circle_inverseFourier_source_eq μ (smoothAngularCap ψ hψ hzero N hN j)
      (integrable_circularPacketAmplitude χ w (sourceWavePacketNormal N j) y k r) y r

end FalconerPacking
