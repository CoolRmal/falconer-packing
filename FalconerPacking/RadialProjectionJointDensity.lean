/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionWeakLimit
public import FalconerPacking.RadialProjectionRay
public import FalconerPacking.PinnedKernel

/-!
# Densities of joint radial laws

The explicit ray density represents each smooth joint law. Absolute continuity of a limiting
joint law identifies its Radon--Nikodym derivative with the canonical radial kernel density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter ProbabilityTheory
open scoped ENNReal Topology

namespace FalconerPacking

/-- The explicit ray density represents the actual joint law of every density source. -/
theorem radialJointProbability_eq_withDensity_ray
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin 2))) = volume.withDensity f) :
    (radialJointProbability κ ν : Measure _) =
      ((κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure).withDensity
        (fun z ↦ radialRayDensity f z.1 z.2) := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  change (∫⁻ z, g z ∂((κ : Measure (EuclideanSpace ℝ (Fin 2))) ⊗ₘ
    radialProjectionKernel (ν : Measure (EuclideanSpace ℝ (Fin 2))))) = _
  rw [Measure.lintegral_compProd hg,
    lintegral_withDensity_eq_lintegral_mul₀
      (measurable_radialRayDensity hf).aemeasurable hg.aemeasurable,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [radialProjectionKernel_apply, hν, map_radialAngle_withDensity_eq hf,
    lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  rfl

/-- Joint absolute continuity gives the actual angular density on almost every pin. -/
theorem ae_radialProjection_absolutelyContinuous_of_joint
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (h : (radialJointProbability κ ν : Measure _) ≪
      (κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure) :
    ∀ᵐ x ∂(κ : Measure (EuclideanSpace ℝ (Fin 2))),
      (ν : Measure (EuclideanSpace ℝ (Fin 2))).map (radialAngle x) ≪ radialAngularMeasure :=
  ae_kernel_absolutelyContinuous_of_compProd h

/-- The canonical radial kernel density also represents the whole joint law. -/
theorem radialJointProbability_eq_withDensity_canonical
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (h : (radialJointProbability κ ν : Measure _) ≪
      (κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure) :
    (radialJointProbability κ ν : Measure _) =
      ((κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure).withDensity
        (fun z ↦ radialProjectionDensity
          (ν : Measure (EuclideanSpace ℝ (Fin 2))) z.1 z.2) := by
  have hac := ae_radialProjection_absolutelyContinuous_of_joint κ ν h
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  change (∫⁻ z, g z ∂((κ : Measure (EuclideanSpace ℝ (Fin 2))) ⊗ₘ
    radialProjectionKernel (ν : Measure (EuclideanSpace ℝ (Fin 2))))) = _
  rw [Measure.lintegral_compProd hg,
    lintegral_withDensity_eq_lintegral_mul₀
      (measurable_radialProjectionDensity
        (ν : Measure (EuclideanSpace ℝ (Fin 2)))).aemeasurable hg.aemeasurable,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hac] with x hx
  rw [radialProjectionKernel_apply, ← withDensity_radialProjectionDensity_eq _ x hx,
    lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  rfl

/-- The joint Radon--Nikodym derivative equals the canonical kernel density almost everywhere. -/
theorem radialProjectionDensity_ae_eq_joint_rnDeriv
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (h : (radialJointProbability κ ν : Measure _) ≪
      (κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure) :
    (fun z ↦ radialProjectionDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) z.1 z.2) =ᵐ[
      (κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure]
      (radialJointProbability κ ν : Measure _).rnDeriv
        ((κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure) := by
  have heq := Measure.rnDeriv_withDensity
    ((κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure)
    (measurable_radialProjectionDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))))
  rw [← radialJointProbability_eq_withDensity_canonical κ ν h] at heq
  exact heq.symm

end FalconerPacking
