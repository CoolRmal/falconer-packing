/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleFourierConvolution
import FalconerPacking.AnnularPinnedReconstruction

/-!
# Joint pinned energy from actual circular energy

The source may depend measurably on the pin. Liu's identity is applied to each actual Schwartz
source, and Tonelli then transfers the integrated spectral-circle estimate to the actual joint
distance densities. Only an upper bound on source-pin distances is needed in this step.
-/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Measurable source families have measurable actual distance densities. -/
theorem measurable_family_complexDistanceDensity
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      complexDistanceDensity (f p.1) p.1 p.2) := by
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      ∫ θ, f p.1 (p.2 • angularDirection θ + p.1) ∂radialAngularMeasure) := by
    have hh : Measurable (fun q : (EuclideanSpace ℝ (Fin 2) × ℝ) × ℝ ↦
        f q.1.1 (q.1.2 • angularDirection q.2 + q.1.1)) := hf.comp
          (show Measurable (fun q : (EuclideanSpace ℝ (Fin 2) × ℝ) × ℝ ↦
            (q.1.1, q.1.2 • angularDirection q.2 + q.1.1)) by fun_prop)
    exact hh.stronglyMeasurable.integral_prod_right.measurable
  unfold complexDistanceDensity pinnedCircularAverage circularAverage
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd) <;> fun_prop

/-- Fourier transforms of measurable integrable families remain jointly measurable. -/
theorem measurable_family_fourier
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      𝓕 (f p.1) p.2) := by
  simp_rw [Real.fourier_eq]
  have hh : Measurable (fun q : (EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2) ↦
      𝐞 (-⟪q.2, q.1.2⟫) • f q.1.1 q.2) := by
    apply Measurable.smul
    · fun_prop
    · exact hf.comp (show Measurable (fun q : (EuclideanSpace ℝ (Fin 2) ×
        EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2) ↦ (q.1.1, q.2)) by fun_prop)
  exact hh.stronglyMeasurable.integral_prod_right.measurable

private theorem measurable_parameter_circleIntegral
    (F : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℂ) (hF : Measurable F) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      ∫ θ, 𝐞 (⟪p.1, p.2 • angularDirection θ⟫) • F (p.1, p.2 • angularDirection θ)
        ∂radialAngularMeasure) := by
  simp_rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  have hh : Measurable (fun q : (EuclideanSpace ℝ (Fin 2) × ℝ) × ℝ ↦
      Complex.exp (((2 * Real.pi * ⟪q.1.1, q.1.2 • angularDirection q.2⟫ : ℝ) : ℂ) *
        Complex.I) *
        F (q.1.1, q.1.2 • angularDirection q.2)) := by
    apply Measurable.mul
    · fun_prop
    · exact hF.comp (show Measurable
        (fun q : (EuclideanSpace ℝ (Fin 2) × ℝ) × ℝ ↦
          (q.1.1, q.1.2 • angularDirection q.2)) by fun_prop)
  exact hh.stronglyMeasurable.integral_prod_right.measurable

/-- The pin-dependent spectral circle averages are jointly measurable. -/
theorem measurable_family_pinnedSpectralCircleAverage
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      pinnedSpectralCircleAverage (f p.1) p.1 p.2) := by
  exact (measurable_parameter_circleIntegral (fun p ↦ 𝓕 (f p.1) p.2)
    (measurable_family_fourier hf)).const_smul ((((2 * Real.pi)⁻¹ : ℝ) : ℂ))

/-- The single-pin unweighted energy estimate, with the actual spectral circle average. -/
theorem integral_complexDistanceDensity_sq_le_spectral
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) {L : ℝ}
    (hL : ∀ x, f x ≠ 0 → dist x y ≤ L) :
    (∫ t, ‖complexDistanceDensity f y t‖ ^ 2) ≤ L * (2 * Real.pi) ^ 2 *
      ∫ r in Ioi (0 : ℝ), r * ‖pinnedSpectralCircleAverage f y r‖ ^ 2 := by
  simpa only [pinnedSpectralCircleAverage_eq_convolution f.integrable] using
    integral_complexDistanceDensity_sq_le_convolution f y hL

/-- Nonnegative-integral form of the single-pin estimate, with no hidden finiteness assumption. -/
theorem lintegral_complexDistanceDensity_sq_le_spectral
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) {L : ℝ} (hL₀ : 0 ≤ L)
    (hL : ∀ x, f x ≠ 0 → dist x y ≤ L) :
    (∫⁻ t, ENNReal.ofReal (‖complexDistanceDensity f y t‖ ^ 2)) ≤
      ENNReal.ofReal (L * (2 * Real.pi) ^ 2) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
          ENNReal.ofReal (‖pinnedSpectralCircleAverage f y r‖ ^ 2) := by
  have hi := (memLp_complexDistanceDensity f y hL).integrable_norm_pow
    (by norm_num : 2 ≠ 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ sq_nonneg _)]
  have he : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
      ENNReal.ofReal (‖pinnedSpectralCircleAverage f y r‖ ^ 2)) =
      ENNReal.ofReal (∫ r in Ioi (0 : ℝ), r * ‖pinnedSpectralCircleAverage f y r‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrableOn_weighted_pinnedSpectralCircleAverage f y)]
    · apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [ENNReal.ofReal_mul hr.le]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_nonneg hr.le (sq_nonneg _)
  rw [he, ← ENNReal.ofReal_mul (mul_nonneg hL₀ (sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (integral_complexDistanceDensity_sq_le_spectral f y hL)

/-- Tonelli and Liu turn an integrated spectral-circle estimate into the actual joint density
energy. The family may depend on the pin through arbitrary measurable selections. -/
theorem lintegral_joint_complexDistanceDensity_sq_le
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hf : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      f p.1 p.2)) {L : ℝ} (hL₀ : 0 ≤ L)
    (hL : ∀ᵐ y ∂ν, ∀ x, f y x ≠ 0 → dist x y ≤ L) :
    (∫⁻ p, ENNReal.ofReal (‖complexDistanceDensity (f p.1) p.1 p.2‖ ^ 2)
      ∂ν.prod volume) ≤ ENNReal.ofReal (L * (2 * Real.pi) ^ 2) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
          ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν := by
  have hd := ((measurable_family_complexDistanceDensity
    (f := fun y x ↦ f y x) hf).norm.pow_const 2).ennreal_ofReal
  have hs := ((measurable_family_pinnedSpectralCircleAverage
    (f := fun y x ↦ f y x) hf).norm.pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hd.aemeasurable]
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (L * (2 * Real.pi) ^ 2) *
        (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
          ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hL] with y hy
      exact lintegral_complexDistanceDensity_sq_le_spectral (f y) y hL₀ hy
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      rw [lintegral_lintegral_swap (by fun_prop : Measurable
        (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦ ENNReal.ofReal p.2 *
          ENNReal.ofReal (‖pinnedSpectralCircleAverage (f p.1) p.1 p.2‖ ^ 2))).aemeasurable]
      apply lintegral_congr
      intro r
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Finite actual spectral energy gives square integrability of the actual joint density. -/
theorem memLp_joint_complexDistanceDensity_of_spectral
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hf : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      f p.1 p.2)) {L : ℝ} (hL₀ : 0 ≤ L)
    (hL : ∀ᵐ y ∂ν, ∀ x, f y x ≠ 0 → dist x y ≤ L)
    (hs : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
      ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) < ∞) :
    MemLp (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      complexDistanceDensity (f p.1) p.1 p.2) 2 (ν.prod volume) := by
  have hm := measurable_family_complexDistanceDensity (f := fun y x ↦ f y x) hf
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine ⟨(hm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  exact (lintegral_joint_complexDistanceDensity_sq_le ν f hf hL₀ hL).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs)

end FalconerPacking
