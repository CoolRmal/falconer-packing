/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionApproximationMoment
public import FalconerPacking.RadialProjectionJointDensity
public import FalconerPacking.WeakMomentLimit
public import FalconerPacking.WeakMomentDensity

/-!
# Averaged radial projection of Frostman probabilities

Actual positive smooth source densities satisfy a uniform moment bound. Their joint radial
laws converge weakly. The resulting positive-power set bound yields absolute continuity and
a smaller moment of the canonical jointly measurable radial density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter ProbabilityTheory
open scoped ENNReal Topology Convolution

namespace FalconerPacking

/-- The explicit shrinking radial density represents the actual smoothed joint law. -/
theorem radialJointProbability_smooth_eq_withDensity_shrinking
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (n : ℕ) :
    (radialJointProbability κ (smoothSourceProbability ν (shrinkingSourceBump n)) : Measure _) =
      ((κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure).withDensity
        (Function.uncurry
          (shrinkingRadialDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) n)) := by
  let φ := shrinkingSourceBump n
  have hf : Measurable (fun x ↦ ENNReal.ofReal
      (smoothMeasureDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) (φ.normed volume) x)) :=
    (contDiff_smoothMeasureDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) φ.contDiff_normed
      φ.hasCompactSupport_normed).continuous.measurable.ennreal_ofReal
  have hdensity : (smoothSourceProbability ν φ : Measure _) =
      volume.withDensity (fun x ↦ ENNReal.ofReal
        (smoothMeasureDensity
          (ν : Measure (EuclideanSpace ℝ (Fin 2))) (φ.normed volume) x)) := by
    change (ν : Measure (EuclideanSpace ℝ (Fin 2))) ∗ smoothBumpMeasure φ = _
    unfold smoothBumpMeasure
    exact (withDensity_smoothMeasureDensity_eq_conv
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) (φ := φ.normed volume)
      φ.contDiff_normed φ.hasCompactSupport_normed φ.nonneg_normed).symm
  unfold Function.uncurry shrinkingRadialDensity
  exact radialJointProbability_eq_withDensity_ray κ (smoothSourceProbability ν φ) hf hdensity

/-- Bounded planar Frostman probabilities of exponents greater than one have actual radial
densities on almost every pin and a finite averaged density moment above order one. -/
theorem exists_radialProjection_density_moment
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {α β Cν Cκ Mν Mκ : ℝ} (hα : 1 < α) (hβ : 1 < β)
    (hCν : 0 < Cν) (hCκ : 0 < Cκ)
    (hν : IsFrostman (ν : Measure (EuclideanSpace ℝ (Fin 2))) α Cν)
    (hκ : IsFrostman (κ : Measure (EuclideanSpace ℝ (Fin 2))) β Cκ)
    (hνsupp : ∀ᵐ x ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))), ‖x‖ ≤ Mν)
    (hκsupp : ∀ᵐ x ∂(κ : Measure (EuclideanSpace ℝ (Fin 2))), ‖x‖ ≤ Mκ) :
    ∃ q : ℝ, 1 < q ∧
      (radialJointProbability κ ν : Measure _) ≪
        (κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure ∧
      (∀ᵐ x ∂(κ : Measure (EuclideanSpace ℝ (Fin 2))),
        (ν : Measure (EuclideanSpace ℝ (Fin 2))).map (radialAngle x) ≪
          radialAngularMeasure) ∧
      (∫⁻ x, (∫⁻ θ,
        radialProjectionDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) x θ ^ q
        ∂radialAngularMeasure) ∂(κ : Measure (EuclideanSpace ℝ (Fin 2)))) < ∞ := by
  obtain ⟨b, c, K, hc, hcb, hK, hmoment⟩ := exists_uniform_shrinking_radial_moment
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) (κ : Measure (EuclideanSpace ℝ (Fin 2)))
    hα hβ hCν hCκ hν hκ hνsupp hκsupp
  have hb : 1 < b := hc.trans hcb
  have hb₀ : 0 < b := by linarith
  let m := (κ : Measure (EuclideanSpace ℝ (Fin 2))).prod radialAngularMeasure
  let f (n : ℕ) := Function.uncurry
    (shrinkingRadialDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) n)
  have hf (n : ℕ) : Measurable (f n) :=
    measurable_shrinkingRadialDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) n
  have hmoment' (n : ℕ) : (∫⁻ z, f n z ^ b ∂m) ≤ K := by
    rw [lintegral_prod _ ((hf n).pow_const b).aemeasurable]
    exact hmoment n
  have hlim := tendsto_radialJointProbability_smoothSource κ ν hα hν
    shrinkingSourceBump tendsto_shrinkingSourceBump_rOut
  have hθ₀ : 0 < (b - 1) / b := div_pos (by linarith) hb₀
  have hθ₁ : (b - 1) / b < 1 := (div_lt_one hb₀).mpr (by linarith)
  have hconstant : K ^ (1 / b) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hb₀.le) hK.ne
  have hbound : ∀ U : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsOpen U →
      (radialJointProbability κ ν : Measure _) U ≤ K ^ (1 / b) * m U ^ ((b - 1) / b) := by
    apply probabilityMeasure_open_power_bound_of_tendsto hlim m _ _
    intro U hU
    exact Eventually.of_forall fun n ↦ by
      rw [radialJointProbability_smooth_eq_withDensity_shrinking]
      apply (withDensity_le_moment_power m (hf n) hb hU.measurableSet).trans
      exact mul_le_mul_left (ENNReal.rpow_le_rpow (hmoment' n)
        (one_div_nonneg.mpr hb₀.le)) _
  have hcexp : c < 1 / (1 - (b - 1) / b) := by
    convert hcb using 1
    field_simp
    ring
  obtain ⟨hac, hRN⟩ := absolutelyContinuous_and_rnDeriv_moment_of_open_power_bound
    hconstant hθ₀ hθ₁ (by linarith : 0 ≤ c) hcexp hbound
  refine ⟨c, hc, hac, ae_radialProjection_absolutelyContinuous_of_joint κ ν hac, ?_⟩
  have hcanonical : (∫⁻ z,
      radialProjectionDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) z.1 z.2 ^ c ∂m) =
      ∫⁻ z, (radialJointProbability κ ν : Measure _).rnDeriv m z ^ c ∂m := by
    apply lintegral_congr_ae
    exact (radialProjectionDensity_ae_eq_joint_rnDeriv κ ν hac).mono fun z hz ↦
      congrArg (fun t : ℝ≥0∞ ↦ t ^ c) hz
  rw [← hcanonical, lintegral_prod _
    ((measurable_radialProjectionDensity
      (ν : Measure (EuclideanSpace ℝ (Fin 2)))).pow_const c).aemeasurable] at hRN
  exact hRN

end FalconerPacking
