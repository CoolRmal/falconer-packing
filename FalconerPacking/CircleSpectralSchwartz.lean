/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.TerminalCircleEnergy
import FalconerPacking.CompactSourceSchwartz

/-!
# Actual Schwartz terminal circle pieces

Compact circle support and a smooth compact spectral bump produce actual Schwartz
convolutions. Fourier inversion and Plancherel transfer the terminal estimate to
physical space without an assumed Fourier representation.
-/

noncomputable section

open MeasureTheory Set SchwartzMap FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Normalized circle measure is concentrated on vectors of norm `|r|`. -/
theorem ae_norm_normalizedCircleMeasure (r : ℝ) :
    ∀ᵐ ξ ∂normalizedCircleMeasure r, ‖ξ‖ ≤ |r| := by
  rw [normalizedCircleMeasure, ae_map_iff (by fun_prop) (by measurability)]
  exact ae_of_all _ fun θ ↦ by simp only [norm_smul, Real.norm_eq_abs,
    norm_angularDirection, mul_one, le_refl]

/-- The actual circle convolution, bundled as a Schwartz function. -/
def circleSpectralSchwartz (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : HasCompactSupport k) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  compactKernelWeightedConvolution (normalizedCircleMeasure r)
    (ae_norm_normalizedCircleMeasure r) hg (k.smooth ⊤) hk

@[simp]
theorem circleSpectralSchwartz_apply (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : HasCompactSupport k) (x : EuclideanSpace ℝ (Fin 2)) :
    circleSpectralSchwartz r hg k hk x = circleSpectralConvolution r g k x := rfl

/-- The physical terminal piece is the actual inverse Fourier transform. -/
def circlePhysicalSchwartz (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : HasCompactSupport k) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  𝓕⁻ (circleSpectralSchwartz r hg k hk)

@[simp]
theorem fourier_circlePhysicalSchwartz (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : HasCompactSupport k) :
    𝓕 (circlePhysicalSchwartz r hg k hk) = circleSpectralSchwartz r hg k hk :=
  fourier_fourierInv_eq _

/-- The actual extension of complex circle spectral data. -/
def circleSpectralExtension (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ∫ ξ, (𝐞 ⟪ξ, x⟫ : ℂ) * g ξ ∂normalizedCircleMeasure r

/-- The inverse spectral convolution is exactly a physical cutoff times circle extension. -/
theorem circlePhysicalSchwartz_apply (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : HasCompactSupport k) (x : EuclideanSpace ℝ (Fin 2)) :
    circlePhysicalSchwartz r hg k hk x =
      (𝓕⁻ k) x * circleSpectralExtension r g x := by
  have hb := hg.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) (k.integrable (μ := volume))
  have hi : Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      𝐞 ⟪p.1, x⟫ • (g p.2 * k (p.1 - p.2)))
      (volume.prod (normalizedCircleMeasure r)) := by
    refine hb.mono ?_ ?_
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hb.aestronglyMeasurable
    · exact ae_of_all _ fun p ↦ by simp only [Circle.norm_smul,
        ContinuousLinearMap.mul_apply', le_refl]
  calc
    _ = ∫ ξ, 𝐞 ⟪ξ, x⟫ • ∫ ζ, g ζ * k (ξ - ζ) ∂normalizedCircleMeasure r := by
      rw [circlePhysicalSchwartz, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
      rfl
    _ = ∫ ξ, ∫ ζ, 𝐞 ⟪ξ, x⟫ • (g ζ * k (ξ - ζ)) ∂normalizedCircleMeasure r := by
      congr 1
      ext ξ
      simp only [Circle.smul_def, integral_smul]
    _ = ∫ ζ, ∫ ξ, 𝐞 ⟪ξ, x⟫ • (g ζ * k (ξ - ζ)) ∂volume
        ∂normalizedCircleMeasure r := integral_integral_swap hi
    _ = ∫ ζ, ∫ η, 𝐞 ⟪ζ + η, x⟫ • (g ζ * k η) ∂volume
        ∂normalizedCircleMeasure r := by
      congr 1
      ext ζ
      convert (integral_sub_right_eq_self
        (fun η ↦ 𝐞 ⟪ζ + η, x⟫ • (g ζ * k η)) ζ (μ := volume)) using 1
      congr 1
      ext ξ
      rw [show ζ + (ξ - ζ) = ξ by abel]
    _ = ∫ ζ, (𝐞 ⟪ζ, x⟫ : ℂ) * g ζ * (𝓕⁻ k) x
        ∂normalizedCircleMeasure r := by
      congr 1
      ext ζ
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, ← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun η ↦ by
        simp only [inner_add_left, AddChar.map_add_eq_mul, Circle.smul_def,
          Circle.coe_mul, smul_eq_mul]
        ring
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

/-- Extended squared-norm Plancherel for actual Schwartz functions. -/
theorem lintegral_schwartz_fourier_norm_sq
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ 2) = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have hf := (f.memLp 2 volume).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hF := ((𝓕 f).memLp 2 volume).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have he := congrArg ENNReal.ofReal (SchwartzMap.integral_norm_sq_fourier f)
  rw [ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ fun _ ↦ sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ ↦ sq_nonneg _)] at he
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using he

/-- The physical and spectral circle pieces have exactly the same squared norm. -/
theorem lintegral_circlePhysicalSchwartz_sq (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : HasCompactSupport k) :
    (∫⁻ x, ‖circlePhysicalSchwartz r hg k hk x‖ₑ ^ 2) =
      ∫⁻ ξ, ‖circleSpectralConvolution r g k ξ‖ₑ ^ 2 := by
  rw [← lintegral_schwartz_fourier_norm_sq, fourier_circlePhysicalSchwartz]
  rfl

/-- Actual physical Schwartz pieces obey the terminal circle estimate. -/
theorem sum_circlePhysicalSchwartz_energy_le {ι : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (I : Finset ι) (m : ι → EuclideanSpace ℝ (Fin 2) → ℂ)
    (hm : ∀ i ∈ I, Measurable (m i))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ Metric.closedBall 0 a)
    {B : ℝ} (hB : ∀ ξ, ∑ i ∈ I, ‖m i ξ‖ ^ 2 ≤ B) :
    (∑ i ∈ I.attach, ∫⁻ x,
      ‖circlePhysicalSchwartz r
        (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (memLp_circle_multiplier_planarMeasureFourier μ r I m hm hB i.property))
        k (HasCompactSupport.of_support_subset_isCompact
          (isCompact_closedBall 0 a) hk) x‖ₑ ^ 2) ≤
      ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) * ENNReal.ofReal B *
        ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
          ∂radialAngularProbability := by
  simp_rw [lintegral_circlePhysicalSchwartz_sq]
  convert sum_terminal_circle_energy_le μ hr ha I m hm k hk hB using 1
  exact Finset.sum_attach I (fun i ↦ ∫⁻ x,
    ‖circleSpectralConvolution r (fun ξ ↦ m i ξ * planarMeasureFourier μ ξ) k x‖ₑ ^ 2)

/-- The explicit cutoff circle extensions satisfy the terminal `r⁻¹` estimate. -/
theorem sum_circleSpectralExtension_cutoff_energy_le {ι : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (I : Finset ι) (m : ι → EuclideanSpace ℝ (Fin 2) → ℂ)
    (hm : ∀ i ∈ I, Measurable (m i))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ Metric.closedBall 0 a)
    {B : ℝ} (hB : ∀ ξ, ∑ i ∈ I, ‖m i ξ‖ ^ 2 ≤ B) :
    (∑ i ∈ I, ∫⁻ x, ‖(𝓕⁻ k) x * circleSpectralExtension r
      (fun ξ ↦ m i ξ * planarMeasureFourier μ ξ) x‖ₑ ^ 2) ≤
      ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) * ENNReal.ofReal B *
        ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
          ∂radialAngularProbability := by
  have hkc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 a) hk
  calc
    _ = ∑ i ∈ I, ∫⁻ x, ‖circleSpectralConvolution r
        (fun ξ ↦ m i ξ * planarMeasureFourier μ ξ) k x‖ₑ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hgi := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (memLp_circle_multiplier_planarMeasureFourier μ r I m hm hB hi)
      simpa only [circlePhysicalSchwartz_apply] using
        lintegral_circlePhysicalSchwartz_sq r hgi k hkc
    _ ≤ _ := sum_terminal_circle_energy_le μ hr ha I m hm k hk hB

end FalconerPacking
