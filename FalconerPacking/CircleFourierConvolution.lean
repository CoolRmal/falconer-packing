/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.LiuPinnedIdentity

/-!
# Circular Fourier convolution in the pinned identity

The spectral circle extension is identified with convolution by the Fourier transform
of normalized circle measure. Its Fubini hypothesis follows from source integrability
and unit-modulus phases. A bounded-distance support condition then converts the weighted
pinned identity into the usual unweighted squared-density estimate.
-/

noncomputable section

open MeasureTheory Set Filter SchwartzMap
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Normalized circle measure, including the radius-zero Dirac measure. -/
def normalizedCircleMeasure (r : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  radialAngularProbability.map (fun θ ↦ r • angularDirection θ)

/-- The actual Fourier transform of normalized circle measure. -/
def circleFourierKernel (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ∫ ξ, (𝐞 (-⟪ξ, z⟫) : ℂ) ∂normalizedCircleMeasure r

theorem circleFourierKernel_eq_angular (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    circleFourierKernel r z =
      ∫ θ, (𝐞 (-⟪r • angularDirection θ, z⟫) : ℂ) ∂radialAngularProbability := by
  rw [circleFourierKernel, normalizedCircleMeasure, integral_map (by fun_prop) (by fun_prop)]

theorem circleFourierKernel_eq_fourierIntegral (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    circleFourierKernel r z = VectorFourier.fourierIntegral 𝐞 (normalizedCircleMeasure r)
      (innerₗ (EuclideanSpace ℝ (Fin 2))) 1 z := by
  simp only [circleFourierKernel, VectorFourier.fourierIntegral, innerₗ_apply_apply,
    Pi.one_apply, Circle.smul_def, smul_eq_mul, mul_one]

/-- Antipodal symmetry permits either sign of the Fourier phase. -/
theorem circleFourierKernel_eq_positive_phase (r : ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    circleFourierKernel r z =
      ∫ θ, (𝐞 (⟪z, r • angularDirection θ⟫) : ℂ) ∂radialAngularProbability := by
  rw [circleFourierKernel_eq_angular]
  have h := integral_circle_add_eq_sub (fun ξ ↦ (𝐞 (⟪z, ξ⟫) : ℂ)) 0 r
  simp only [add_zero, zero_sub, inner_neg_right] at h
  simp only [radialAngularProbability, integral_smul_measure]
  congr 1
  simpa only [real_inner_comm] using h.symm

/-- The normalized circle Fourier kernel is bounded by one. -/
theorem norm_circleFourierKernel_le_one (r : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖circleFourierKernel r z‖ ≤ 1 := by
  rw [circleFourierKernel_eq_angular]
  simpa using norm_integral_le_of_norm_le_const (μ := radialAngularProbability)
    (C := 1) (ae_of_all _ fun _ ↦ by simp)

theorem pinnedSpectralCircleAverage_eq_probability
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    pinnedSpectralCircleAverage f y r = ∫ θ,
      𝐞 (⟪y, r • angularDirection θ⟫) • 𝓕 f (r • angularDirection θ)
        ∂radialAngularProbability := by
  simp [pinnedSpectralCircleAverage, radialAngularProbability, integral_smul_measure,
    ENNReal.toReal_inv, Real.pi_pos.le, RCLike.real_smul_eq_coe_mul]

/-- The actual spectral circle average equals convolution with the circle Fourier kernel. -/
theorem pinnedSpectralCircleAverage_eq_convolution
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    pinnedSpectralCircleAverage f y r = ∫ x, f x * circleFourierKernel r (y - x) := by
  have hp : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ f p.2)
      (radialAngularProbability.prod volume) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℂ) (μ := radialAngularProbability)).mul_prod hf
  have hc : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      𝐞 (⟪y - p.2, r • angularDirection p.1⟫)) := by fun_prop
  have hi : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      𝐞 (⟪y - p.2, r • angularDirection p.1⟫) • f p.2)
      (radialAngularProbability.prod volume) := by
    rw [← integrable_norm_iff (hc.aestronglyMeasurable.fun_smul hp.aestronglyMeasurable)]
    simpa only [Circle.norm_smul] using hp.norm
  rw [pinnedSpectralCircleAverage_eq_probability]
  calc
    _ = ∫ θ, ∫ x, 𝐞 (⟪y - x, r • angularDirection θ⟫) • f x
        ∂volume ∂radialAngularProbability := by
      apply integral_congr_ae
      refine ae_of_all _ fun θ ↦ ?_
      dsimp only
      rw [Real.fourier_eq, Circle.smul_def, ← integral_smul]
      apply integral_congr_ae
      refine ae_of_all _ fun x ↦ ?_
      dsimp only
      rw [inner_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul]
      simp only [Circle.smul_def, Circle.coe_mul, smul_eq_mul, mul_assoc]
    _ = ∫ x, ∫ θ, 𝐞 (⟪y - x, r • angularDirection θ⟫) • f x
        ∂radialAngularProbability ∂volume := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      refine ae_of_all _ fun x ↦ ?_
      dsimp only
      rw [circleFourierKernel_eq_positive_phase]
      simp only [Circle.smul_def, smul_eq_mul]
      rw [integral_mul_const, mul_comm]

/-- The pinned quadratic identity in its circular-convolution form. -/
theorem liu_pinned_identity_convolution
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (∫ t in Ioi (0 : ℝ), ‖complexDistanceDensity f y t‖ ^ 2 / t) =
      (2 * Real.pi) ^ 2 * ∫ r in Ioi (0 : ℝ),
        r * ‖∫ x, f x * circleFourierKernel r (y - x)‖ ^ 2 := by
  rw [liu_pinned_identity]
  simp_rw [pinnedSpectralCircleAverage_eq_convolution f.integrable]

@[fun_prop]
theorem measurable_complexDistanceDensity
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f)
    (y : EuclideanSpace ℝ (Fin 2)) : Measurable (complexDistanceDensity f y) := by
  have hm : Measurable (pinnedCircularAverage f y) :=
    measurable_circularAverage (hf.comp (measurable_id.add_const y))
  unfold complexDistanceDensity
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id) <;> fun_prop

/-- Bounded source-pin distances give an actual upper support bound for the circle density. -/
theorem complexDistanceDensity_eq_zero_of_lt
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} {y : EuclideanSpace ℝ (Fin 2)} {R t : ℝ}
    (hR : ∀ x, f x ≠ 0 → dist x y ≤ R) (htR : R < t) :
    complexDistanceDensity f y t = 0 := by
  by_cases ht : 0 < t
  · rw [complexDistanceDensity_eq_circle_integral f y ht]
    have hz : (fun θ ↦ f (y - t • angularDirection θ)) = (fun _ ↦ 0) := by
      funext θ
      by_contra h
      have hdist : dist (y - t • angularDirection θ) y = t := by
        rw [dist_comm, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs,
          norm_angularDirection, mul_one, abs_of_pos ht]
      exact (not_le.mpr htR) (hdist ▸ hR _ h)
    rw [hz, integral_zero, mul_zero]
  · simp only [complexDistanceDensity, ht, ↓reduceIte]

/-- On positive radii the ordinary density energy is bounded by `R` times the weighted energy. -/
theorem complexDistanceDensity_sq_le_weighted
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} {y : EuclideanSpace ℝ (Fin 2)} {R t : ℝ}
    (hR : ∀ x, f x ≠ 0 → dist x y ≤ R) (ht : 0 < t) :
    ‖complexDistanceDensity f y t‖ ^ 2 ≤ R * (‖complexDistanceDensity f y t‖ ^ 2 / t) := by
  by_cases h : t ≤ R
  · calc
      _ = t * (‖complexDistanceDensity f y t‖ ^ 2 / t) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h (div_nonneg (sq_nonneg _) ht.le)
  · rw [complexDistanceDensity_eq_zero_of_lt hR (lt_of_not_ge h)]
    simp

/-- Bounded-distance Schwartz sources have an actual square-integrable distance density. -/
theorem memLp_complexDistanceDensity
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) {R : ℝ}
    (hR : ∀ x, f x ≠ 0 → dist x y ≤ R) :
    MemLp (complexDistanceDensity f y) 2 volume := by
  have hm : AEStronglyMeasurable (complexDistanceDensity f y) volume :=
    (measurable_complexDistanceDensity f.continuous.measurable y).aestronglyMeasurable
  have hs : IntegrableOn (fun t ↦ ‖complexDistanceDensity f y t‖ ^ 2)
      (Ioi (0 : ℝ)) volume := by
    apply ((integrableOn_complexDistanceDensity_sq_div f y).const_mul R).mono'
      (hm.norm.pow 2).restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm] using
      complexDistanceDensity_sq_le_weighted hR ht
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have heq : (Ioi (0 : ℝ)).indicator (fun t ↦ ‖complexDistanceDensity f y t‖ ^ 2) =
      (fun t ↦ ‖complexDistanceDensity f y t‖ ^ 2) := by
    funext t
    by_cases ht : 0 < t <;> simp [ht, complexDistanceDensity]
  rw [← heq]
  exact (integrable_indicator_iff measurableSet_Ioi).2 hs

/-- The unweighted pinned `L²` bound used for bounded source-pin distances. -/
theorem integral_complexDistanceDensity_sq_le_convolution
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) {R : ℝ}
    (hR : ∀ x, f x ≠ 0 → dist x y ≤ R) :
    (∫ t, ‖complexDistanceDensity f y t‖ ^ 2) ≤
      R * (2 * Real.pi) ^ 2 * ∫ r in Ioi (0 : ℝ),
        r * ‖∫ x, f x * circleFourierKernel r (y - x)‖ ^ 2 := by
  have heq : (Ioi (0 : ℝ)).indicator (fun t ↦ ‖complexDistanceDensity f y t‖ ^ 2) =
      (fun t ↦ ‖complexDistanceDensity f y t‖ ^ 2) := by
    funext t
    by_cases ht : 0 < t <;> simp [ht, complexDistanceDensity]
  calc
    _ = ∫ t in Ioi (0 : ℝ), ‖complexDistanceDensity f y t‖ ^ 2 := by
      rw [← integral_indicator measurableSet_Ioi, heq]
    _ ≤ ∫ t in Ioi (0 : ℝ), R * (‖complexDistanceDensity f y t‖ ^ 2 / t) := by
      apply integral_mono_ae
        (((memLp_complexDistanceDensity f y hR).integrable_norm_pow
          (by norm_num : 2 ≠ 0)).restrict)
        ((integrableOn_complexDistanceDensity_sq_div f y).const_mul R)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact complexDistanceDensity_sq_le_weighted hR ht
    _ = R * ∫ t in Ioi (0 : ℝ), ‖complexDistanceDensity f y t‖ ^ 2 / t :=
      integral_const_mul _ _
    _ = _ := by rw [liu_pinned_identity_convolution, mul_assoc]

end FalconerPacking
