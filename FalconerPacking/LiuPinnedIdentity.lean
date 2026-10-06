/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircularPlancherel
public import FalconerPacking.DistancePolarDensity

/-!
# The pinned circular Plancherel identity

Translation supplies the exact Fourier phase at a pin. Circular Plancherel then
identifies weighted distance-density energy with weighted spectral circle energy,
including the normalization constant. The nonnegative case is identified with
the actual pinned-distance pushforward measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter SchwartzMap
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Normalized mean of the source over the circle centered at the pin. -/
def pinnedCircularAverage (f : EuclideanSpace ℝ (Fin 2) → ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) : ℂ :=
  circularAverage (fun x ↦ f (x + y)) r

/-- The normalized spectral circle extension in mathlib's `2π` Fourier convention. -/
def pinnedSpectralCircleAverage (f : EuclideanSpace ℝ (Fin 2) → ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) : ℂ :=
  (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • ∫ θ,
    𝐞 (⟪y, r • angularDirection θ⟫) • 𝓕 f (r • angularDirection θ) ∂radialAngularMeasure

/-- Classical translation gives the exact phase in the pinned spectral circle average. -/
theorem circularAverage_fourier_translate (f : EuclideanSpace ℝ (Fin 2) → ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    circularAverage (𝓕 (fun x ↦ f (x + y))) r = pinnedSpectralCircleAverage f y r := by
  have h := VectorFourier.fourierIntegral_comp_add_right 𝐞 volume
    (innerₗ (EuclideanSpace ℝ (Fin 2))) f y
  change 𝓕 (fun x ↦ f (x + y)) = (fun ξ ↦ 𝐞 (⟪y, ξ⟫) • 𝓕 f ξ) at h
  rw [h]
  rfl

/-- Circular Plancherel translated to an arbitrary pin. -/
theorem pinnedCircularAverage_plancherel
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (∫ r in Ioi (0 : ℝ), r * ‖pinnedCircularAverage f y r‖ ^ 2) =
      ∫ r in Ioi (0 : ℝ), r * ‖pinnedSpectralCircleAverage f y r‖ ^ 2 := by
  have h := circularAverage_plancherel (f.compSubConstCLM ℂ (-y))
  have ht : (f.compSubConstCLM ℂ (-y) : EuclideanSpace ℝ (Fin 2) → ℂ) =
      (fun x ↦ f (x + y)) := by
    funext x
    simp only [compSubConstCLM_apply, sub_neg_eq_add]
  rw [ht] at h
  simpa only [pinnedCircularAverage, circularAverage_fourier_translate] using h

/-- The complex circle density, with the Jacobian of the distance map and zero negative part. -/
def complexDistanceDensity (f : EuclideanSpace ℝ (Fin 2) → ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℂ :=
  if 0 < t then ((2 * Real.pi * t : ℝ) : ℂ) * pinnedCircularAverage f y t else 0

/-- The radial Jacobian produces the reciprocal-radius weight in the pinned identity. -/
theorem complexDistanceDensity_sq_div
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (y : EuclideanSpace ℝ (Fin 2))
    {t : ℝ} (ht : 0 < t) :
    ‖complexDistanceDensity f y t‖ ^ 2 / t =
      (2 * Real.pi) ^ 2 * (t * ‖pinnedCircularAverage f y t‖ ^ 2) := by
  simp only [complexDistanceDensity, ht, ↓reduceIte, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos ht]
  field_simp
  ring

/-- Liu's pinned quadratic identity, with explicit radius powers and normalization. -/
theorem liu_pinned_identity
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (∫ t in Ioi (0 : ℝ), ‖complexDistanceDensity f y t‖ ^ 2 / t) =
      (2 * Real.pi) ^ 2 *
        ∫ r in Ioi (0 : ℝ), r * ‖pinnedSpectralCircleAverage f y r‖ ^ 2 := by
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        (2 * Real.pi) ^ 2 * (t * ‖pinnedCircularAverage f y t‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact complexDistanceDensity_sq_div f y ht
    _ = (2 * Real.pi) ^ 2 * ∫ t in Ioi (0 : ℝ),
        t * ‖pinnedCircularAverage f y t‖ ^ 2 := integral_const_mul _ _
    _ = _ := by rw [pinnedCircularAverage_plancherel]

/-- Changing direction to its antipode reverses the sign of the unit vector. -/
theorem angularDirection_add_pi (θ : ℝ) :
    angularDirection (θ + Real.pi) = -angularDirection θ := by
  simp only [angularDirection, Real.cos_add_pi, Real.sin_add_pi,
    Complex.ofReal_neg, neg_mul, ← neg_add, map_neg]

/-- Plus and minus conventions for circles give precisely the same Bochner integral. -/
theorem integral_circle_add_eq_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin 2) → E) (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    (∫ θ, f (r • angularDirection θ + y) ∂radialAngularMeasure) =
      ∫ θ, f (y - r • angularDirection θ) ∂radialAngularMeasure := by
  have hp : Function.Periodic (fun θ ↦ f (r • angularDirection θ + y))
      (2 * Real.pi) := by
    intro θ
    simp only [angularDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have h := integral_radialAngularMeasure_comp_add hp Real.pi
  simp only [angularDirection_add_pi, smul_neg, neg_add_eq_sub] at h
  exact h.symm

/-- The complex density is the unnormalized circle integral times the radius. -/
theorem complexDistanceDensity_eq_circle_integral
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (y : EuclideanSpace ℝ (Fin 2)) {t : ℝ}
    (ht : 0 < t) :
    complexDistanceDensity f y t = (t : ℂ) *
      ∫ θ, f (y - t • angularDirection θ) ∂radialAngularMeasure := by
  rw [complexDistanceDensity, if_pos ht, pinnedCircularAverage, circularAverage,
    integral_circle_add_eq_sub]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp

/-- For continuous nonnegative sources the circle density agrees pointwise with the
positive polar density, including its prescribed zero value at nonpositive radii. -/
theorem distancePolarDensity_eq_ofReal_complexDistanceDensity
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Continuous f) (hf₀ : ∀ x, 0 ≤ f x)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    distancePolarDensity (fun x ↦ ENNReal.ofReal (f x)) y t =
      ENNReal.ofReal (complexDistanceDensity (fun x ↦ (f x : ℂ)) y t).re := by
  by_cases ht : 0 < t
  · have hc : Continuous (fun θ ↦ f (y - t • angularDirection θ)) := by fun_prop
    have hi : Integrable (fun θ ↦ f (y - t • angularDirection θ)) radialAngularMeasure :=
      hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [distancePolarDensity, if_pos ht, complexDistanceDensity_eq_circle_integral _ _ ht,
      integral_complex_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re,
      ENNReal.ofReal_mul ht.le,
      ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun θ ↦ hf₀ _)]
  · simp only [distancePolarDensity, complexDistanceDensity, ht, ↓reduceIte,
      Complex.zero_re, ENNReal.ofReal_zero]

/-- The nonnegative complex circle formula represents the actual pinned-distance law. -/
theorem map_dist_withDensity_eq_complexDistanceDensity
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Continuous f) (hf₀ : ∀ x, 0 ≤ f x)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))).map (fun x ↦ dist x y) =
      volume.withDensity (fun t ↦
        ENNReal.ofReal (complexDistanceDensity (fun x ↦ (f x : ℂ)) y t).re) := by
  rw [map_dist_withDensity_eq (by fun_prop) y]
  congr 1
  funext t
  exact distancePolarDensity_eq_ofReal_complexDistanceDensity hf hf₀ y t

/-- The translated physical circle energy is finite. -/
theorem integrableOn_weighted_pinnedCircularAverage
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    IntegrableOn (fun r ↦ r * ‖pinnedCircularAverage f y r‖ ^ 2) (Ioi (0 : ℝ)) volume := by
  let F := f.compSubConstCLM ℂ (-y)
  have h := integrableOn_weighted_circularAverage F.continuous.measurable
    F.integrable (F.memLp 2 volume)
  have heq : (F : EuclideanSpace ℝ (Fin 2) → ℂ) = (fun x ↦ f (x + y)) := by
    funext x
    simp only [F, compSubConstCLM_apply, sub_neg_eq_add]
  simpa only [heq, pinnedCircularAverage] using h

/-- The translated spectral circle energy is finite. -/
theorem integrableOn_weighted_pinnedSpectralCircleAverage
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    IntegrableOn (fun r ↦ r * ‖pinnedSpectralCircleAverage f y r‖ ^ 2)
      (Ioi (0 : ℝ)) volume := by
  let F := f.compSubConstCLM ℂ (-y)
  have h := integrableOn_weighted_circularAverage (𝓕 F).continuous.measurable
    (𝓕 F).integrable ((𝓕 F).memLp 2 volume)
  have heq : (F : EuclideanSpace ℝ (Fin 2) → ℂ) = (fun x ↦ f (x + y)) := by
    funext x
    simp only [F, compSubConstCLM_apply, sub_neg_eq_add]
  simpa only [SchwartzMap.fourier_coe, heq, circularAverage_fourier_translate] using h

/-- The reciprocal-radius weighted distance-density energy is an actual finite integral. -/
theorem integrableOn_complexDistanceDensity_sq_div
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    IntegrableOn (fun t ↦ ‖complexDistanceDensity f y t‖ ^ 2 / t)
      (Ioi (0 : ℝ)) volume := by
  apply ((integrableOn_weighted_pinnedCircularAverage f y).const_mul
    ((2 * Real.pi) ^ 2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (complexDistanceDensity_sq_div f y ht).symm

end FalconerPacking
