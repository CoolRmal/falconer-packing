/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionLine
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Fourier transform and angular averaging

Planar rotations are actual volume-preserving linear isometries. Their joint action
transfers almost-everywhere measurability, and its angular fibers all have the same
first norm. This proves the product integrability needed for Fubini directly from
integrability of the source function, without a uniform-integrability hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Rotation through the given angle, expressed in the fixed Euclidean coordinates. -/
def planarRotation (θ : ℝ) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.symm.trans (angularCartesianFrame θ)

theorem planarRotation_apply (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    planarRotation θ x = Complex.orthonormalBasisOneI.repr
      (Complex.exp (θ * Complex.I) * Complex.orthonormalBasisOneI.repr.symm x) := rfl

@[fun_prop]
theorem continuous_planarRotation :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ planarRotation p.1 p.2) := by
  simp only [planarRotation_apply]
  fun_prop

/-- A measurable angle parameter and a planar point are rotated without creating null-set mass. -/
theorem quasiMeasurePreserving_planarRotation (ν : Measure ℝ) :
    Measure.QuasiMeasurePreserving
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ planarRotation p.1 p.2)
      (ν.prod volume) volume :=
  QuasiMeasurePreserving.prod_of_right continuous_planarRotation.measurable
    (ae_of_all _ fun θ ↦ (planarRotation θ).measurePreserving.quasiMeasurePreserving)

/-- Every rotation fiber has precisely the original first norm. -/
theorem integral_norm_planarRotation (f : EuclideanSpace ℝ (Fin 2) → ℂ) (θ : ℝ) :
    (∫ x, ‖f (planarRotation θ x)‖) = ∫ x, ‖f x‖ :=
  (planarRotation θ).measurePreserving.integral_comp
    (planarRotation θ).toHomeomorph.measurableEmbedding (fun x ↦ ‖f x‖)

/-- Finite angular measure and one integrable source give the actual joint Fubini hypothesis. -/
theorem integrable_planarRotation_prod (ν : Measure ℝ) [IsFiniteMeasure ν]
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Integrable f volume) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ f (planarRotation p.1 p.2))
      (ν.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ f (planarRotation p.1 p.2))
      (ν.prod volume) := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_planarRotation ν)
  apply (integrable_prod_iff hm).2
  refine ⟨ae_of_all _ (fun θ ↦ ?_), ?_⟩
  · exact ((planarRotation θ).measurePreserving.integrable_comp hf.aestronglyMeasurable).2 hf
  · simp_rw [integral_norm_planarRotation]
    exact integrable_const _

/-- The angular integral itself is an integrable function of the planar point. -/
theorem integrable_planarRotation_integral (ν : Measure ℝ) [IsFiniteMeasure ν]
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Integrable f volume) :
    Integrable (fun x ↦ ∫ θ, f (planarRotation θ x) ∂ν) volume :=
  (integrable_planarRotation_prod ν hf).integral_prod_right

/-- Fourier transformation commutes with every finite angular average of actual rotations. -/
theorem fourier_planarRotation_integral (ν : Measure ℝ) [IsFiniteMeasure ν]
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Integrable f volume)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun x ↦ ∫ θ, f (planarRotation θ x) ∂ν) ξ =
      ∫ θ, 𝓕 f (planarRotation θ ξ) ∂ν := by
  have hrot := integrable_planarRotation_prod ν hf
  have hc : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ 𝐞 (-⟪p.2, ξ⟫)) := by
    fun_prop
  have hphase : Integrable
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ 𝐞 (-⟪p.2, ξ⟫) •
        f (planarRotation p.1 p.2)) (ν.prod volume) := by
    rw [← integrable_norm_iff (hc.aestronglyMeasurable.fun_smul hrot.aestronglyMeasurable)]
    simpa only [Circle.norm_smul] using hrot.norm
  calc
    _ = ∫ x, ∫ θ, 𝐞 (-⟪x, ξ⟫) • f (planarRotation θ x) ∂ν := by
      rw [Real.fourier_eq]
      simp only [Circle.smul_def, integral_smul]
    _ = ∫ θ, ∫ x, 𝐞 (-⟪x, ξ⟫) • f (planarRotation θ x) ∂volume ∂ν :=
      (integral_integral_swap hphase).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun θ ↦ Real.fourier_comp_linearIsometry (planarRotation θ) f ξ

/-- The normalized full-turn angular average of a complex planar function. -/
def radialFourierAverage (f : EuclideanSpace ℝ (Fin 2) → ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • ∫ θ, f (planarRotation θ x) ∂radialAngularMeasure

/-- Normalized radial averaging preserves integrability. -/
theorem integrable_radialFourierAverage {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Integrable f volume) : Integrable (radialFourierAverage f) volume := by
  exact (integrable_planarRotation_integral radialAngularMeasure hf).smul
    ((((2 * Real.pi)⁻¹ : ℝ) : ℂ))

/-- The normalized angular average commutes pointwise with the planar Fourier transform. -/
theorem fourier_radialFourierAverage {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Integrable f volume) (ξ : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (radialFourierAverage f) ξ = radialFourierAverage (𝓕 f) ξ := by
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ (EuclideanSpace ℝ (Fin 2)))
    (((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) •
      (fun x ↦ ∫ θ, f (planarRotation θ x) ∂radialAngularMeasure)) ξ = _
  rw [VectorFourier.fourierIntegral_const_smul]
  change (((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
    𝓕 (fun x ↦ ∫ θ, f (planarRotation θ x) ∂radialAngularMeasure) ξ = _
  rw [fourier_planarRotation_integral radialAngularMeasure hf ξ]
  rfl

end FalconerPacking
