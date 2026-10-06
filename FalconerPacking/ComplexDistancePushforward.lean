/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircleFourierConvolution

/-!
# Complex pinned-distance densities

The circle formula is an integrable density for every measurable integrable complex
source. Its integral against every bounded measurable test is exactly the source
test under the distance map. This supplies the signed and complex pushforward
identification needed when applying the pinned identity to wave packets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The planar Bochner polar formula in the fixed Euclidean coordinates. -/
theorem integral_polar_euclidean (f : EuclideanSpace ℝ (Fin 2) → ℂ) :
    (∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • f (p.1 • angularDirection p.2)) = ∫ x, f x := by
  have h := Complex.integral_comp_polarCoord_symm
    (fun z ↦ f (Complex.orthonormalBasisOneI.repr z))
  have he := Complex.orthonormalBasisOneI.repr.measurePreserving.integral_comp
    Complex.orthonormalBasisOneI.repr.toHomeomorph.measurableEmbedding f
  rw [he] at h
  simpa only [polarCoord_target, Complex.polarCoord_symm_apply,
    angularDirection, ← Complex.real_smul, map_smul, smul_eq_mul] using h

/-- Source integrability gives the actual Fubini hypothesis after polar change of variables. -/
theorem integrable_polar_euclidean {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Measurable f) (hi : Integrable f volume) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (p.1 • angularDirection p.2))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) volume := by
  refine ⟨(by fun_prop : Measurable (fun p : ℝ × ℝ ↦
    p.1 • f (p.1 • angularDirection p.2))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * ENNReal.ofReal (‖f (p.1 • angularDirection p.2)‖) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1, ENNReal.ofReal_mul hp.1.le]
    _ = ∫⁻ x, ENNReal.ofReal ‖f x‖ :=
      lintegral_polar_euclidean (fun x ↦ ENNReal.ofReal ‖f x‖)
    _ < ⊤ := (hasFiniteIntegral_iff_norm f).1 hi.2

private theorem circle_integral_eq_complexDistanceDensity
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (y : EuclideanSpace ℝ (Fin 2))
    {t : ℝ} (ht : 0 < t) :
    (∫ θ in Ioo (-Real.pi) Real.pi, t • f (t • angularDirection θ + y)) =
      complexDistanceDensity f y t := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, integral_smul]
  change t • (∫ θ, f (t • angularDirection θ + y) ∂radialAngularMeasure) = _
  rw [integral_circle_add_eq_sub, complexDistanceDensity_eq_circle_integral f y ht]
  simp only [Complex.real_smul]

/-- The complex distance density is integrable whenever the actual source is integrable. -/
theorem integrable_complexDistanceDensity
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) (hi : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) : Integrable (complexDistanceDensity f y) volume := by
  have hp := integrable_polar_euclidean (hf.comp (measurable_id.add_const y))
    (hi.comp_add_right y)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hp
  have hs : IntegrableOn (complexDistanceDensity f y) (Ioi (0 : ℝ)) volume := by
    apply hp.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact circle_integral_eq_complexDistanceDensity f y ht
  have heq : (Ioi (0 : ℝ)).indicator (complexDistanceDensity f y) =
      complexDistanceDensity f y := by
    funext t
    by_cases ht : 0 < t <;> simp [complexDistanceDensity, ht]
  rw [← heq]
  exact (integrable_indicator_iff measurableSet_Ioi).2 hs

/-- The complex circle density has exactly the source's integral. -/
theorem integral_complexDistanceDensity
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) (hi : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) : (∫ t, complexDistanceDensity f y t) = ∫ x, f x := by
  have hp := integrable_polar_euclidean (hf.comp (measurable_id.add_const y))
    (hi.comp_add_right y)
  have heq : (Ioi (0 : ℝ)).indicator (complexDistanceDensity f y) =
      complexDistanceDensity f y := by
    funext t
    by_cases ht : 0 < t <;> simp [complexDistanceDensity, ht]
  calc
    _ = ∫ t in Ioi (0 : ℝ), complexDistanceDensity f y t := by
      rw [← integral_indicator measurableSet_Ioi, heq]
    _ = ∫ t in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        t • f (t • angularDirection θ + y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (circle_integral_eq_complexDistanceDensity f y ht).symm
    _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • f (p.1 • angularDirection p.2 + y) := by
      rw [Measure.volume_eq_prod]
      rw [Measure.volume_eq_prod] at hp
      exact (setIntegral_prod _ hp).symm
    _ = ∫ x, f (x + y) := integral_polar_euclidean (fun x ↦ f (x + y))
    _ = _ := integral_add_right_eq_self f y

/-- Multiplying the source by a distance test multiplies its exact circle density. -/
theorem complexDistanceDensity_mul_dist
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (g : ℝ → ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    complexDistanceDensity (fun x ↦ f x * g (dist x y)) y t =
      complexDistanceDensity f y t * g t := by
  by_cases ht : 0 < t
  · rw [complexDistanceDensity_eq_circle_integral _ _ ht,
      complexDistanceDensity_eq_circle_integral _ _ ht]
    have hd (θ : ℝ) : dist (y - t • angularDirection θ) y = t := by
      rw [dist_comm, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs,
        norm_angularDirection, mul_one, abs_of_pos ht]
    simp only [hd, integral_mul_const, mul_assoc]
  · simp only [complexDistanceDensity, ht, ↓reduceIte, zero_mul]

/-- Both sides of the pushforward test identity are absolutely integrable. -/
theorem complexDistanceDensity_test_integrable
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) (hi : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) {g : ℝ → ℂ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    Integrable (fun t ↦ complexDistanceDensity f y t * g t) volume ∧
      Integrable (fun x ↦ f x * g (dist x y)) volume := by
  exact ⟨(integrable_complexDistanceDensity hf hi y).mul_bdd hg.aestronglyMeasurable
    (ae_of_all _ hB), hi.mul_bdd (hg.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ hB _)⟩

/-- The actual complex density represents the distance pushforward on every bounded
measurable test, not just on nonnegative sources. -/
theorem integral_complexDistanceDensity_mul_test
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) (hi : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) {g : ℝ → ℂ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    (∫ t, complexDistanceDensity f y t * g t) = ∫ x, f x * g (dist x y) := by
  have hgi : Integrable (fun x ↦ f x * g (dist x y)) volume :=
    hi.mul_bdd (hg.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ hB _)
  have h := integral_complexDistanceDensity (by fun_prop) hgi y
  simpa only [complexDistanceDensity_mul_dist] using h

/-- Taking absolute values is bounded by the positive circle density of the source norm. -/
theorem norm_complexDistanceDensity_le
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ‖complexDistanceDensity f y t‖ ≤
      (complexDistanceDensity (fun x ↦ (‖f x‖ : ℂ)) y t).re := by
  by_cases ht : 0 < t
  · rw [complexDistanceDensity_eq_circle_integral _ _ ht,
      complexDistanceDensity_eq_circle_integral _ _ ht, integral_complex_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) ht.le
  · simp only [complexDistanceDensity, ht, ↓reduceIte, norm_zero, Complex.zero_re, le_refl]

/-- The actual complex pinned pushforward contracts the first norm. -/
theorem integral_norm_complexDistanceDensity_le
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) (hi : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (∫ t, ‖complexDistanceDensity f y t‖) ≤ ∫ x, ‖f x‖ := by
  have hm : Measurable (fun x ↦ (‖f x‖ : ℂ)) := by fun_prop
  have hn := integrable_complexDistanceDensity hm hi.norm.ofReal y
  calc
    _ ≤ ∫ t, (complexDistanceDensity (fun x ↦ (‖f x‖ : ℂ)) y t).re :=
      integral_mono_ae (integrable_complexDistanceDensity hf hi y).norm hn.re
        (ae_of_all _ fun t ↦ norm_complexDistanceDensity_le f y t)
    _ = _ := by
      change (∫ t, RCLike.re (complexDistanceDensity (fun x ↦ (‖f x‖ : ℂ)) y t)) = _
      rw [integral_re hn, integral_complexDistanceDensity hm hi.norm.ofReal y,
        integral_complex_ofReal]
      rfl

end FalconerPacking
