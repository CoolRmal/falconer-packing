/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialFourierAverage
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Plancherel for normalized radial averages

Rotation invariance and Jensen's inequality give contraction of the actual normalized
angular average in `L²`. Fourier duality identifies the classical transform with the
`L²` transform whenever both classical functions belong to `L²`. Consequently the
radial average of a Schwartz function satisfies Plancherel, without any assumption
that its angular integral is itself a Schwartz function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter SchwartzMap
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Probability measure for a full turn in the fixed angular chart. -/
def radialAngularProbability : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • radialAngularMeasure

instance : IsProbabilityMeasure radialAngularProbability where
  measure_univ := by
    simp only [radialAngularProbability, Measure.smul_apply, smul_eq_mul,
      radialAngularMeasure, Measure.restrict_apply_univ, Real.volume_Ioc,
      sub_neg_eq_add, ← two_mul]
    exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

/-- The normalization in `radialFourierAverage` is exactly probability averaging. -/
theorem radialFourierAverage_eq_integral (f : EuclideanSpace ℝ (Fin 2) → ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    radialFourierAverage f x =
      ∫ θ, f (planarRotation θ x) ∂radialAngularProbability := by
  simp [radialFourierAverage, radialAngularProbability, integral_smul_measure,
    ENNReal.toReal_inv, Real.pi_pos.le,
    RCLike.real_smul_eq_coe_mul]

/-- Squared norms remain integrable under the joint rotation action. -/
theorem integrable_sq_norm_planarRotation_prod (ν : Measure ℝ) [IsFiniteMeasure ν]
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      ‖f (planarRotation p.1 p.2)‖ ^ 2) (ν.prod volume) := by
  have hsq : Integrable (fun x ↦ ‖f x‖ ^ 2) volume :=
    hf.integrable_norm_pow (by norm_num)
  have hm := hsq.aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_planarRotation ν)
  apply (integrable_prod_iff hm).2
  refine ⟨ae_of_all _ (fun θ ↦ ?_), ?_⟩
  · exact ((planarRotation θ).measurePreserving.integrable_comp
      hsq.aestronglyMeasurable).2 hsq
  · have heq (θ : ℝ) : (∫ x, ‖‖f (planarRotation θ x)‖ ^ 2‖) =
        ∫ x, ‖‖f x‖ ^ 2‖ :=
      (planarRotation θ).measurePreserving.integral_comp
        (planarRotation θ).toHomeomorph.measurableEmbedding (fun x ↦ ‖‖f x‖ ^ 2‖)
    change Integrable (fun θ ↦ ∫ x, ‖‖f (planarRotation θ x)‖ ^ 2‖) ν
    simp_rw [heq]
    exact integrable_const _

/-- The pointwise Jensen bound holds at almost every radius and direction. -/
theorem radialFourierAverage_sq_norm_le {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, ‖radialFourierAverage f x‖ ^ 2 ≤
      ∫ θ, ‖f (planarRotation θ x)‖ ^ 2 ∂radialAngularProbability := by
  have h₁ := (integrable_planarRotation_prod radialAngularProbability hf₁).prod_left_ae
  have h₂ :=
    (integrable_sq_norm_planarRotation_prod radialAngularProbability hf₂).prod_left_ae
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  rw [radialFourierAverage_eq_integral]
  exact (convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2).map_integral_le
    (by fun_prop) isClosed_univ (ae_of_all _ fun _ ↦ mem_univ _) hx₁ hx₂

/-- Normalized radial averaging preserves square-integrability. -/
theorem memLp_radialFourierAverage {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    MemLp (radialFourierAverage f) 2 volume := by
  have hm := (integrable_radialFourierAverage hf₁).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have hsq := integrable_sq_norm_planarRotation_prod radialAngularProbability hf₂
  apply hsq.integral_prod_right.mono' (hm.norm.pow 2)
  filter_upwards [radialFourierAverage_sq_norm_le hf₁ hf₂] with x hx
  simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm] using hx

/-- The squared `L²` energy cannot increase under normalized radial averaging. -/
theorem integral_sq_norm_radialFourierAverage_le {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    (∫ x, ‖radialFourierAverage f x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  have hsq := integrable_sq_norm_planarRotation_prod radialAngularProbability hf₂
  calc
    _ ≤ ∫ x, ∫ θ, ‖f (planarRotation θ x)‖ ^ 2 ∂radialAngularProbability :=
      integral_mono_ae ((memLp_radialFourierAverage hf₁ hf₂).integrable_norm_pow
        (by norm_num)) hsq.integral_prod_right (radialFourierAverage_sq_norm_le hf₁ hf₂)
    _ = ∫ θ, ∫ x, ‖f (planarRotation θ x)‖ ^ 2 ∂volume ∂radialAngularProbability :=
      (integral_integral_swap hsq).symm
    _ = ∫ θ, (∫ x, ‖f x‖ ^ 2) ∂radialAngularProbability := by
      apply integral_congr_ae
      exact ae_of_all _ fun θ ↦ (planarRotation θ).measurePreserving.integral_comp
        (planarRotation θ).toHomeomorph.measurableEmbedding (fun x ↦ ‖f x‖ ^ 2)
    _ = _ := by simp

/-- Classical and `L²` Fourier transforms agree when the classical transform is square-integrable.
The proof uses actual integrable Fourier duality, rather than assumed norm equality. -/
theorem fourier_toLp_eq_of_integrable {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    (hF₂ : MemLp (𝓕 f) 2 volume) :
    𝓕 (hf₂.toLp f) = hF₂.toLp (𝓕 f) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2))))))
  change ((𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) :
    TemperedDistribution (EuclideanSpace ℝ (Fin 2)) ℂ) =
      (hF₂.toLp (𝓕 f) : TemperedDistribution (EuclideanSpace ℝ (Fin 2)) ℂ)
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext φ
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x, (𝓕 φ) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      simp only [hx, smul_eq_mul]
    _ = ∫ x, φ x * 𝓕 f x := by
      have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (μ := volume) (ν := volume)
        (L := innerₗ (EuclideanSpace ℝ (Fin 2))) Real.continuous_fourierChar
        continuous_inner hf₁ φ.integrable
      have hflip : (innerₗ (EuclideanSpace ℝ (Fin 2))).flip =
          innerₗ (EuclideanSpace ℝ (Fin 2)) := by simp
      rw [hflip] at h
      change (∫ ξ, 𝓕 f ξ * φ ξ) = ∫ x, f x * (𝓕 φ) x at h
      calc
        _ = ∫ x, f x * (𝓕 φ) x := by simp only [mul_comm]
        _ = ∫ ξ, 𝓕 f ξ * φ ξ := h.symm
        _ = _ := by simp only [mul_comm]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF₂.coeFn_toLp] with x hx
      simp only [hx, smul_eq_mul]

/-- Express planar squared energy through the genuine `L²` seminorm. -/
theorem integral_sq_norm_eq_eLpNorm_planar {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : MemLp f 2 volume) :
    (∫ x, ‖f x‖ ^ 2) = (eLpNorm f 2 volume).toReal ^ 2 := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf,
    ENNReal.toReal_ofReal (by positivity)]
  norm_num
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg ‖f x‖))]

/-- Normalized radial averaging is a contraction for the actual `L²` seminorm. -/
theorem eLpNorm_radialFourierAverage_le {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    eLpNorm (radialFourierAverage f) 2 volume ≤ eLpNorm f 2 volume := by
  have h₂ := memLp_radialFourierAverage hf₁ hf₂
  apply (ENNReal.toReal_le_toReal h₂.eLpNorm_ne_top hf₂.eLpNorm_ne_top).1
  have h := integral_sq_norm_radialFourierAverage_le hf₁ hf₂
  rw [integral_sq_norm_eq_eLpNorm_planar h₂, integral_sq_norm_eq_eLpNorm_planar hf₂] at h
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (radialFourierAverage f) 2 volume),
    ENNReal.toReal_nonneg (a := eLpNorm f 2 volume)]

/-- Plancherel for an actual integrable function with a square-integrable Fourier integral. -/
theorem integral_sq_norm_fourier_eq_of_integrable
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf₁ : Integrable f volume)
    (hf₂ : MemLp f 2 volume) (hF₂ : MemLp (𝓕 f) 2 volume) :
    (∫ ξ, ‖𝓕 f ξ‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  rw [integral_sq_norm_eq_eLpNorm_planar hF₂, integral_sq_norm_eq_eLpNorm_planar hf₂]
  have h := Lp.norm_fourier_eq (hf₂.toLp f)
  rw [fourier_toLp_eq_of_integrable hf₁ hf₂ hF₂, Lp.norm_toLp, Lp.norm_toLp] at h
  exact congrArg (fun r : ℝ ↦ r ^ 2) h

/-- Radialized Plancherel in planar coordinates, for the actual angular averages of a
Schwartz function and its Fourier transform. No Schwartz regularity of the average is assumed. -/
theorem radialFourierAverage_plancherel
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫ x, ‖radialFourierAverage f x‖ ^ 2) =
      ∫ ξ, ‖radialFourierAverage (𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)) ξ‖ ^ 2 := by
  have h₁ := integrable_radialFourierAverage f.integrable
  have h₂ := memLp_radialFourierAverage f.integrable (f.memLp 2 volume)
  have hF : MemLp (𝓕 (radialFourierAverage f)) 2 volume := by
    have heq : 𝓕 (radialFourierAverage f) =
        radialFourierAverage (𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)) := by
      funext ξ
      exact fourier_radialFourierAverage f.integrable ξ
    rw [heq]
    simpa only [SchwartzMap.fourier_coe] using
      memLp_radialFourierAverage (𝓕 f).integrable ((𝓕 f).memLp 2 volume)
  calc
    _ = ∫ ξ, ‖𝓕 (radialFourierAverage f) ξ‖ ^ 2 :=
      (integral_sq_norm_fourier_eq_of_integrable h₁ h₂ hF).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ξ ↦ by
        dsimp only
        rw [fourier_radialFourierAverage f.integrable ξ]

end FalconerPacking
