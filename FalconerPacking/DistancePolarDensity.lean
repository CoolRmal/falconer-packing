/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialProjectionRay

/-!
# Exact polar density of pinned distance laws

For a nonnegative planar density, the pinned distance density is its circle integral
times the radial Jacobian. The formula is jointly measurable in the pin and radius and
represents the full pushforward measure. All identities use the proved polar change of
variables and apply without Fourier estimates or integrability assumptions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The positive-radius circle integral with its actual planar polar Jacobian. -/
def distancePolarDensity (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ≥0∞ :=
  if 0 < t then ENNReal.ofReal t * ∫⁻ θ, f (y - t • angularDirection θ)
    ∂radialAngularMeasure else 0

@[fun_prop]
theorem measurable_distancePolarDensity {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      distancePolarDensity f p.1 p.2) := by
  unfold distancePolarDensity
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd) <;> fun_prop

/-- Nonpositive distances have zero density, including the origin. -/
theorem distancePolarDensity_eq_zero_of_nonpos
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (y : EuclideanSpace ℝ (Fin 2))
    {t : ℝ} (ht : t ≤ 0) : distancePolarDensity f y t = 0 := by
  simp only [distancePolarDensity, not_lt.mpr ht, ↓reduceIte]

/-- Testing the explicit density against an arbitrary nonnegative measurable function
recovers the original pinned-distance test integral. -/
theorem lintegral_mul_distancePolarDensity
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (y : EuclideanSpace ℝ (Fin 2)) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t, g t * distancePolarDensity f y t) = ∫⁻ x, g (dist x y) * f x := by
  let F : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun v ↦ g (dist (y - v) y) * f (y - v)
  have hpolar := lintegral_polar_euclidean F
  have hsource : (∫⁻ v, F v) = ∫⁻ x, g (dist x y) * f x :=
    lintegral_sub_left_eq_self (fun x ↦ g (dist x y) * f x) y
  rw [hsource] at hpolar
  have hcut : (fun t ↦ g t * distancePolarDensity f y t) =
      (Ioi (0 : ℝ)).indicator (fun t ↦ g t * (ENNReal.ofReal t *
        ∫⁻ θ, f (y - t • angularDirection θ) ∂radialAngularMeasure)) := by
    funext t
    by_cases ht : 0 < t <;> simp [distancePolarDensity, ht]
  rw [hcut, lintegral_indicator measurableSet_Ioi]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal t * (g t * f (y - t • angularDirection θ)) := by
      apply lintegral_congr
      intro t
      rw [radialAngularMeasure, ← setLIntegral_congr Ioo_ae_eq_Ioc,
        ← mul_assoc, ← lintegral_const_mul (g t * ENNReal.ofReal t) (by fun_prop)]
      apply lintegral_congr
      intro θ
      ac_rfl
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * (g p.1 * f (y - p.1 • angularDirection p.2)) := by
      rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * F (p.1 • angularDirection p.2) := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hd : dist (y - p.1 • angularDirection p.2) y = p.1 := by
        rw [dist_comm, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs,
          norm_angularDirection, mul_one, abs_of_pos hp.1]
      simp only [F, hd]
    _ = _ := hpolar

/-- The circle formula is the density of the entire pinned-distance pushforward. -/
theorem map_dist_withDensity_eq
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (volume.withDensity f).map (fun x ↦ dist x y) =
      volume.withDensity (distancePolarDensity f y) := by
  apply Measure.ext
  intro A hA
  have hdist : Measurable (fun x : EuclideanSpace ℝ (Fin 2) ↦ dist x y) := by fun_prop
  rw [Measure.map_apply hdist hA, withDensity_apply _ (hdist hA), withDensity_apply _ hA]
  have h := lintegral_mul_distancePolarDensity hf y
    (g := A.indicator 1) (measurable_const.indicator hA)
  rw [← lintegral_indicator hA, ← lintegral_indicator (hdist hA)]
  convert h.symm using 1
  · apply lintegral_congr
    intro x
    by_cases hx : dist x y ∈ A <;> simp [hx]
  · apply lintegral_congr
    intro t
    by_cases ht : t ∈ A <;> simp [ht]

/-- Every pin has exactly the original total source mass. -/
theorem lintegral_distancePolarDensity
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ t, distancePolarDensity f y t) = ∫⁻ x, f x := by
  simpa only [one_mul] using
    lintegral_mul_distancePolarDensity hf y (g := fun _ ↦ 1) measurable_const

/-- Finite source mass gives an integrable real representative of each explicit density. -/
theorem integrable_distancePolarDensity_toReal
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ x, f x) ≠ ∞) (y : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun t ↦ (distancePolarDensity f y t).toReal) volume := by
  have hm : Measurable (distancePolarDensity f y) :=
    (measurable_distancePolarDensity hf).comp (measurable_const.prodMk measurable_id)
  apply integrable_toReal_of_lintegral_ne_top hm.aemeasurable
  rwa [lintegral_distancePolarDensity hf y]

/-- Integrating the real representative preserves its exact finite total mass. -/
theorem integral_distancePolarDensity_toReal
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ x, f x) ≠ ∞) (y : EuclideanSpace ℝ (Fin 2)) :
    (∫ t, (distancePolarDensity f y t).toReal) = (∫⁻ x, f x).toReal := by
  have hm : Measurable (distancePolarDensity f y) :=
    (measurable_distancePolarDensity hf).comp (measurable_const.prodMk measurable_id)
  have hmass : (∫⁻ t, distancePolarDensity f y t) ≠ ∞ := by
    rwa [lintegral_distancePolarDensity hf y]
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hmass), lintegral_distancePolarDensity hf y]

/-- With finite source mass, passing to the real representative keeps the full pushforward law. -/
theorem map_dist_withDensity_eq_toReal
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ x, f x) ≠ ∞) (y : EuclideanSpace ℝ (Fin 2)) :
    (volume.withDensity f).map (fun x ↦ dist x y) = volume.withDensity
      (fun t ↦ ENNReal.ofReal (distancePolarDensity f y t).toReal) := by
  rw [map_dist_withDensity_eq hf y]
  apply withDensity_congr_ae
  have hm : Measurable (distancePolarDensity f y) :=
    (measurable_distancePolarDensity hf).comp (measurable_const.prodMk measurable_id)
  have hmass : (∫⁻ t, distancePolarDensity f y t) ≠ ∞ := by
    rwa [lintegral_distancePolarDensity hf y]
  filter_upwards [ae_lt_top hm hmass] with t ht
  exact (ENNReal.ofReal_toReal ht.ne).symm

/-- The exact polar identity also holds for vector-valued tests, including Fourier phases. -/
theorem integral_smul_distancePolarDensity_toReal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ x, f x) ≠ ∞) (y : EuclideanSpace ℝ (Fin 2))
    (g : ℝ → E)
    (hg : AEStronglyMeasurable g ((volume.withDensity f).map (fun x ↦ dist x y))) :
    (∫ t, (distancePolarDensity f y t).toReal • g t) =
      ∫ x, (f x).toReal • g (dist x y) := by
  have hm : Measurable (distancePolarDensity f y) :=
    (measurable_distancePolarDensity hf).comp (measurable_const.prodMk measurable_id)
  have hmass : (∫⁻ t, distancePolarDensity f y t) ≠ ∞ := by
    rwa [lintegral_distancePolarDensity hf y]
  rw [← integral_withDensity_eq_integral_toReal_smul hm (ae_lt_top hm hmass) g,
    ← map_dist_withDensity_eq hf y, integral_map (by fun_prop) hg,
    integral_withDensity_eq_integral_toReal_smul hf (ae_lt_top hf hfin)]

/-- Integrating over any pin measure gives the full joint distance law with the same density. -/
theorem map_joint_dist_withDensity_eq
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) :
    (ν.prod (volume.withDensity f)).map (fun p ↦ (p.1, dist p.2 p.1)) =
      (ν.prod volume).withDensity (fun p ↦ distancePolarDensity f p.1 p.2) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (by fun_prop), lintegral_prod _ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_distancePolarDensity hf) hg,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro y
  rw [lintegral_withDensity_eq_lintegral_mul _ hf (by fun_prop)]
  simp only [Pi.mul_apply]
  simpa only [mul_comm] using
    (lintegral_mul_distancePolarDensity hf y
      (g := fun t ↦ g (y, t)) (hg.comp (measurable_const.prodMk measurable_id))).symm

end FalconerPacking
