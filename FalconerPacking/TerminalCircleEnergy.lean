/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircleSpectralConvolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Terminal circle energy of finite source measures

The circle convolution estimate is applied to the actual Fourier transform of a
finite measure and an arbitrary finite multiplier family with bounded square sum.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SchwartzMap
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The planar Fourier transform in the `2π` normalization. -/
def planarMeasureFourier (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  VectorFourier.fourierIntegral 𝐞 μ (innerₗ (EuclideanSpace ℝ (Fin 2))) 1 ξ

/-- Agreement with the characteristic function after its normalization dilation. -/
theorem planarMeasureFourier_eq_charFun
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (ξ : EuclideanSpace ℝ (Fin 2)) :
    planarMeasureFourier μ ξ = charFun μ ((-2 * Real.pi) • ξ) := by
  simp only [planarMeasureFourier, VectorFourier.fourierIntegral, innerₗ_apply_apply,
    Circle.smul_def, Pi.one_apply, Real.fourierChar_apply, smul_eq_mul, mul_one,
    charFun_apply, inner_smul_right]
  congr 1
  funext x
  congr 1
  push_cast
  ring

theorem continuous_planarMeasureFourier
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] :
    Continuous (planarMeasureFourier μ) := by
  change Continuous (fun ξ ↦ planarMeasureFourier μ ξ)
  simp_rw [planarMeasureFourier_eq_charFun]
  exact continuous_charFun.comp (by fun_prop)

/-- Every finite source has bounded Fourier transform. -/
theorem norm_planarMeasureFourier_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖planarMeasureFourier μ ξ‖ ≤ μ.real univ := by
  rw [planarMeasureFourier_eq_charFun]
  exact norm_charFun_le _

/-- The actual circular Fourier energy equals the normalized angular integral. -/
theorem circle_planarMeasureFourier_energy_eq_angular
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (r : ℝ) :
    (∫⁻ ξ, ‖planarMeasureFourier μ ξ‖ₑ ^ 2 ∂normalizedCircleMeasure r) =
      ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
        ∂radialAngularProbability := by
  rw [normalizedCircleMeasure, lintegral_map
    ((continuous_planarMeasureFourier μ).measurable.enorm.pow_const 2) (by fun_prop)]

/-- A real square-sum bound controls each multiplier on every circle. -/
theorem memLp_circle_multiplier_planarMeasureFourier {ι : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (r : ℝ) (I : Finset ι) (m : ι → EuclideanSpace ℝ (Fin 2) → ℂ)
    (hm : ∀ i ∈ I, Measurable (m i))
    {B : ℝ} (hB : ∀ ξ, ∑ i ∈ I, ‖m i ξ‖ ^ 2 ≤ B)
    {i : ι} (hi : i ∈ I) :
    MemLp (fun ξ ↦ m i ξ * planarMeasureFourier μ ξ) 2
      (normalizedCircleMeasure r) := by
  apply MemLp.of_bound
    ((hm i hi).mul (continuous_planarMeasureFourier μ).measurable).aestronglyMeasurable
    (Real.sqrt B * μ.real univ)
  filter_upwards [] with ξ
  change ‖m i ξ * planarMeasureFourier μ ξ‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (Real.le_sqrt_of_sq_le
    ((Finset.single_le_sum (fun j hj ↦ sq_nonneg ‖m j ξ‖) hi).trans (hB ξ)))
    (norm_planarMeasureFourier_le μ ξ) (norm_nonneg _) (Real.sqrt_nonneg _)

/-- The terminal quadratic estimate contains the actual circular source energy and no
factor for the number of spectral labels. -/
theorem sum_terminal_circle_energy_le {ι : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (I : Finset ι) (m : ι → EuclideanSpace ℝ (Fin 2) → ℂ)
    (hm : ∀ i ∈ I, Measurable (m i))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ Metric.closedBall 0 a)
    {B : ℝ} (hB : ∀ ξ, ∑ i ∈ I, ‖m i ξ‖ ^ 2 ≤ B) :
    (∑ i ∈ I, ∫⁻ x,
      ‖circleSpectralConvolution r (fun ξ ↦ m i ξ * planarMeasureFourier μ ξ) k x‖ₑ ^ 2) ≤
      ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) * ENNReal.ofReal B *
        ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
          ∂radialAngularProbability := by
  rw [← circle_planarMeasureFourier_energy_eq_angular]
  apply sum_lintegral_circleSpectralConvolution_sq_le hr ha I m hm
    (continuous_planarMeasureFourier μ).measurable k hk
  intro ξ
  have h := ENNReal.ofReal_le_ofReal (hB ξ)
  rw [ENNReal.ofReal_sum_of_nonneg (fun j hj ↦ sq_nonneg ‖m j ξ‖)] at h
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

/-- Each term in the terminal estimate is the squared norm of an actual `L²` function. -/
theorem memLp_terminal_circle_convolution {ι : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (I : Finset ι) (m : ι → EuclideanSpace ℝ (Fin 2) → ℂ)
    (hm : ∀ i ∈ I, Measurable (m i))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ Metric.closedBall 0 a)
    {B : ℝ} (hB : ∀ ξ, ∑ i ∈ I, ‖m i ξ‖ ^ 2 ≤ B)
    {i : ι} (hi : i ∈ I) :
    MemLp (circleSpectralConvolution r
      (fun ξ ↦ m i ξ * planarMeasureFourier μ ξ) k) 2 volume :=
  memLp_circleSpectralConvolution hr ha
    ((hm i hi).mul (continuous_planarMeasureFourier μ).measurable)
    (memLp_circle_multiplier_planarMeasureFourier μ r I m hm hB hi) k hk

end FalconerPacking
