/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SourcePacketFrequency
import FalconerPacking.SpatialStripFourier

/-!
# The actual Fourier convolution and microlocal tails of source packets

The Fourier transform of each spatially cut off source packet is an ordinary convolution.
Uniform anisotropic decay of the spatial cutoff therefore controls the actual frequency
leakage, including pointwise on each frequency circle.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Absolute Fubini for the spatial Fourier transform of the cut-off source convolution. -/
theorem integrable_cutoff_sourceFourier_prod
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (ζ : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      Complex.exp ((-2 * Real.pi * ⟪p.1, ζ⟫ : ℝ) * Complex.I) *
        (K p.1 * (Complex.exp ((2 * Real.pi * ⟪p.2, p.1⟫ : ℝ) * Complex.I) *
          sourcePacketSpectrum μ ψ p.2))) (volume.prod volume) := by
  apply (K.integrable.norm.mul_prod (integrable_sourcePacketSpectrum μ ψ).norm).mono'
  · apply Continuous.aestronglyMeasurable
    exact (by fun_prop : Continuous (fun p :
      EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
        Complex.exp ((-2 * Real.pi * ⟪p.1, ζ⟫ : ℝ) * Complex.I))).mul
      ((K.continuous.comp continuous_fst).mul
        ((by fun_prop : Continuous (fun p :
          EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
            Complex.exp ((2 * Real.pi * ⟪p.2, p.1⟫ : ℝ) * Complex.I))).mul
          ((continuous_sourcePacketSpectrum μ ψ).comp continuous_snd)))
  · exact ae_of_all _ fun p ↦ by
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- Exact Fourier convolution for any Schwartz spatial cutoff and finite source measure. -/
theorem fourier_cutoff_inverseFourier_source_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ψ K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (ζ : EuclideanSpace ℝ (Fin 2)) :
    (𝓕 (fun x ↦ K x * ∫ z, (𝓕⁻ ψ) (x - z) ∂μ)) ζ =
      ∫ ξ, (𝓕 K) (ζ - ξ) * sourcePacketSpectrum μ ψ ξ := by
  rw [Real.fourier_eq']
  simp_rw [integral_inverseFourier_source_eq μ ψ, smul_eq_mul, ← integral_const_mul]
  rw [integral_integral_swap (integrable_cutoff_sourceFourier_prod μ ψ K ζ)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [SchwartzMap.fourier_coe, Real.fourier_eq', ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [mul_left_comm (K x), ← mul_assoc, ← Complex.exp_add]
  have he : ((-2 * Real.pi * ⟪x, ζ⟫ : ℝ) : ℂ) * Complex.I +
      ((2 * Real.pi * ⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I =
      ((-2 * Real.pi * ⟪x, ζ - ξ⟫ : ℝ) : ℂ) * Complex.I := by
    rw [inner_sub_right, real_inner_comm x ξ]
    push_cast
    ring
  rw [he]
  ring

/-- The Fourier transform of an actual source packet is the actual convolution, not a
function assumed to have cap support. -/
theorem fourier_sourceWavePacket_eq_convolution
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (j : ℕ) (k : ℤ)
    (ζ : EuclideanSpace ℝ (Fin 2)) :
    (𝓕 (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k)) ζ =
      ∫ ξ, (𝓕 (spatialStripCutoff χ hχ w (sourceWavePacketNormal N j) k)) (ζ - ξ) *
        sourcePacketSpectrum μ (smoothAngularCap ψ hψ hzero N hN j) ξ := by
  rw [SchwartzMap.fourier_coe]
  exact fourier_cutoff_inverseFourier_source_eq μ
    (smoothAngularCap ψ hψ hzero N hN j)
    (spatialStripCutoff χ hχ w (sourceWavePacketNormal N j) k) ζ

/-- Every frequency outside an anisotropic neighborhood of the original cap has a rapid
pointwise bound. In particular this controls its trace on any frequency circle. -/
theorem exists_sourceWavePacket_fourier_tail_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
        (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
        (N : ℕ) (hN : 0 < N) (j : ℕ)
        (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)),
        (∀ x, ⟪sourceWavePacketNormal N j, x⟫ = O x 0) →
        ∀ w : ℝ, 0 < w → w ≤ 1 → ∀ (k : ℤ) (ζ : EuclideanSpace ℝ (Fin 2)) (H : ℝ),
          0 ≤ H →
          (∀ ξ ∈ Function.support (smoothAngularCap ψ hψ hzero N hN j),
            H ≤ ‖(WithLp.toLp 2 ![w * (O (ζ - ξ)) 0, (O (ζ - ξ)) 1] :
              EuclideanSpace ℝ (Fin 2))‖) →
          ‖(𝓕 (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k)) ζ‖ ≤
            (w * C / (1 + H) ^ m) * μ.real univ *
              ∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ := by
  obtain ⟨C, hC, hc⟩ := exists_spatialStripCutoff_fourier_decay χ hχ m
  refine ⟨C, hC, ?_⟩
  intro μ _ M hμ ψ hψ hzero N hN j O hO w hw hw₁ k ζ H hH hsep
  rw [fourier_sourceWavePacket_eq_convolution]
  let cap := smoothAngularCap ψ hψ hzero N hN j
  calc
    _ ≤ ∫ ξ, ((w * C / (1 + H) ^ m) * μ.real univ) * ‖cap ξ‖ := by
      apply norm_integral_le_of_norm_le (cap.integrable.norm.const_mul _)
      apply ae_of_all
      intro ξ
      by_cases hξ : cap ξ = 0
      · change ‖_ * sourcePacketSpectrum μ cap ξ‖ ≤ _
        simp only [sourcePacketSpectrum, hξ, zero_mul, mul_zero, norm_zero, le_refl]
      · have hsupport : ξ ∈ Function.support (smoothAngularCap ψ hψ hzero N hN j) := hξ
        have hk := hc O (sourceWavePacketNormal N j) hO w hw hw₁ k (ζ - ξ)
        have htail : ‖(𝓕 (spatialStripCutoff χ hχ w (sourceWavePacketNormal N j) k))
            (ζ - ξ)‖ ≤ w * C / (1 + H) ^ m := by
          apply hk.trans
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ (by positivity) (by linarith [hsep ξ hsupport]) m)
        rw [norm_mul]
        exact (mul_le_mul htail (norm_sourcePacketSpectrum_le μ cap ξ)
          (norm_nonneg _) (by positivity)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end FalconerPacking
