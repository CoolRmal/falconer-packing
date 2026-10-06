/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionKernel

/-!
# Radial densities from the polar change of variables

For a Lebesgue-density source the radial density is the positive-ray integral with
its radial Jacobian. The formula uses oriented rays, so no identification of opposite
directions or full-line polar identity is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Radial angle of a point on a positive ray, on the chosen angular chart. -/
theorem radialAngle_ray (x : EuclideanSpace ℝ (Fin 2)) {r θ : ℝ}
    (hr : 0 < r) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    radialAngle x (x - r • angularDirection θ) = θ := by
  simp only [radialAngle, sub_sub_cancel, angularDirection, map_smul,
    LinearIsometryEquiv.symm_apply_apply, Complex.real_smul]
  rw [Complex.arg_real_mul _ hr]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_cos_add_sin_mul_I hθ

/-- Positive-ray integral including the polar Jacobian. -/
def radialRayDensity (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * f (x - r • angularDirection θ)

@[fun_prop]
theorem measurable_radialRayDensity {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦ radialRayDensity f p.1 p.2) := by
  unfold radialRayDensity
  fun_prop

/-- The polar formula tested against an arbitrary nonnegative measurable angular function. -/
theorem lintegral_radialRayDensity {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hf : Measurable f) (x : EuclideanSpace ℝ (Fin 2))
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ θ, g θ * radialRayDensity f x θ ∂radialAngularMeasure) =
      ∫⁻ y, g (radialAngle x y) * f y := by
  let F : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
    fun v ↦ g (radialAngle x (x - v)) * f (x - v)
  have hpolar := lintegral_polar_euclidean F
  have hsource : (∫⁻ v, F v) = ∫⁻ y, g (radialAngle x y) * f y :=
    lintegral_sub_left_eq_self (fun y ↦ g (radialAngle x y) * f y) x
  rw [hsource] at hpolar
  calc
    (∫⁻ θ, g θ * radialRayDensity f x θ ∂radialAngularMeasure) =
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal r * (g θ * f (x - r • angularDirection θ)) := by
      rw [radialAngularMeasure, ← setLIntegral_congr Ioo_ae_eq_Ioc]
      apply lintegral_congr
      intro θ
      rw [radialRayDensity, ← lintegral_const_mul (g θ) (by fun_prop)]
      apply lintegral_congr
      intro r
      ac_rfl
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * (g p.2 * f (x - p.1 • angularDirection p.2)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      symm
      apply lintegral_prod_symm
      fun_prop
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * F (p.1 • angularDirection p.2) := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      simp only [F, radialAngle_ray x hp.1 ⟨hp.2.1, hp.2.2.le⟩]
    _ = ∫⁻ y, g (radialAngle x y) * f y := hpolar

/-- The pushforward of a Lebesgue-density source has its explicit, jointly measurable ray density. -/
theorem map_radialAngle_withDensity_eq {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hf : Measurable f) (x : EuclideanSpace ℝ (Fin 2)) :
    (volume.withDensity f).map (radialAngle x) =
      radialAngularMeasure.withDensity (radialRayDensity f x) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_radialAngle.of_uncurry_left hS,
    withDensity_apply _ (measurable_radialAngle.of_uncurry_left hS),
    withDensity_apply _ hS]
  have h := lintegral_radialRayDensity hf x
    (g := S.indicator 1) (measurable_const.indicator hS)
  rw [← lintegral_indicator hS, ← lintegral_indicator
    (measurable_radialAngle.of_uncurry_left hS)]
  convert h.symm using 1
  · apply lintegral_congr
    intro y
    by_cases hy : radialAngle x y ∈ S <;> simp [hy]
  · apply lintegral_congr
    intro θ
    by_cases hθ : θ ∈ S <;> simp [hθ]

/-- A bounded radial Jacobian turns the positive ray into a full-line upper bound. -/
theorem radialRayDensity_le_lineIntegral
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (x : EuclideanSpace ℝ (Fin 2)) {R : ℝ}
    (hR : ∀ y, f y ≠ 0 → dist x y ≤ R) (θ : ℝ) :
    radialRayDensity f x θ ≤
      ENNReal.ofReal R * ∫⁻ r : ℝ, f (x - r • angularDirection θ) := by
  calc
    radialRayDensity f x θ ≤
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal R * f (x - r • angularDirection θ) := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro r hr
      by_cases hz : f (x - r • angularDirection θ) = 0
      · simp [hz]
      have hdist : dist x (x - r • angularDirection θ) = r := by
        simp only [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs,
          norm_angularDirection, mul_one, abs_of_pos (show 0 < r from hr)]
      have hrR : r ≤ R := by simpa only [hdist] using hR _ hz
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hrR) le_rfl
    _ = ENNReal.ofReal R * ∫⁻ r in Ioi (0 : ℝ), f (x - r • angularDirection θ) :=
      lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal R * ∫⁻ r : ℝ, f (x - r • angularDirection θ) :=
      mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- The averaged radial moment of a Lebesgue-density source is bounded by full-line moments.
The pin measure remains the actual, possibly singular, measure. -/
theorem lintegral_radialRayDensity_rpow_le
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] {R p : ℝ} (hp : 0 ≤ p)
    (hR : ∀ᵐ x ∂ν, ∀ y, f y ≠ 0 → dist x y ≤ R) :
    (∫⁻ x, ∫⁻ θ, radialRayDensity f x θ ^ p ∂radialAngularMeasure ∂ν) ≤
      ENNReal.ofReal R ^ p * ∫⁻ θ, ∫⁻ x,
        (∫⁻ r : ℝ, f (x - r • angularDirection θ)) ^ p ∂ν ∂radialAngularMeasure := by
  calc
    (∫⁻ x, ∫⁻ θ, radialRayDensity f x θ ^ p ∂radialAngularMeasure ∂ν) ≤
        ∫⁻ x, ∫⁻ θ, ENNReal.ofReal R ^ p *
          (∫⁻ r : ℝ, f (x - r • angularDirection θ)) ^ p ∂radialAngularMeasure ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hR] with x hx
      apply lintegral_mono
      intro θ
      have h := ENNReal.rpow_le_rpow (radialRayDensity_le_lineIntegral hf x hx θ) hp
      simpa only [ENNReal.mul_rpow_of_nonneg _ _ hp] using h
    _ = ENNReal.ofReal R ^ p * ∫⁻ θ, ∫⁻ x,
          (∫⁻ r : ℝ, f (x - r • angularDirection θ)) ^ p ∂ν ∂radialAngularMeasure := by
      simp_rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)]
      congr 1
      exact lintegral_lintegral_swap (by fun_prop)

end FalconerPacking
