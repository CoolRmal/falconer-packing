/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.FrostmanLineNull
import FalconerPacking.SmoothApproximationTests
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Weak convergence of actual joint radial laws

The angular branch cut is null for a Frostman source of exponent greater than one.
Consequently smoothing that source preserves the weak limit of the joint pin-angle law.
-/

noncomputable section

open MeasureTheory Set Function Filter ProbabilityTheory
open scoped ENNReal Topology

namespace FalconerPacking

/-- The actual probability law of a pin and its radial angle toward an independent source. -/
def radialJointProbability
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  ⟨(κ : Measure _) ⊗ₘ radialProjectionKernel (ν : Measure _), inferInstance⟩

/-- Bounded continuous joint tests can be evaluated before the radial pushforward. -/
theorem integral_radialJointProbability
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2) × ℝ) ℝ) :
    (∫ z, g z ∂(radialJointProbability κ ν : Measure _)) =
      ∫ x, ∫ y, g (x, radialAngle x y) ∂(ν : Measure _) ∂(κ : Measure _) := by
  change (∫ z, g z ∂((κ : Measure _) ⊗ₘ radialProjectionKernel (ν : Measure _))) = _
  rw [Measure.integral_compProd (g.integrable
    (μ := (κ : Measure _) ⊗ₘ radialProjectionKernel (ν : Measure _)))]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    dsimp only
    rw [radialProjectionKernel_apply]
    exact integral_map measurable_radialAngle.of_uncurry_left.aemeasurable
      (g.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

/-- Smoothing the angular source gives weak convergence of the actual joint radial laws. -/
theorem tendsto_radialJointProbability_smoothSource
    (κ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {s C : ℝ} (hs : 1 < s) (hν : IsFrostman (ν : Measure _) s C)
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)))
    (hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n ↦ radialJointProbability κ (smoothSourceProbability ν (φ n)))
      atTop (𝓝 (radialJointProbability κ ν)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  simp_rw [integral_radialJointProbability]
  apply tendsto_joint_integral_smoothSource_of_ae_continuousAt
    (κ : Measure _) ν φ hφ (g := fun x y ↦ g (x, radialAngle x y))
    (g.continuous.measurable.comp (measurable_fst.prodMk measurable_radialAngle))
    (fun x y ↦ g.norm_coe_le_norm (x, radialAngle x y))
  exact Eventually.of_forall fun x ↦
    (ae_continuousAt_radialAngle_of_isFrostman hs hν x).mono fun y hy ↦
      g.continuous.continuousAt.comp (continuousAt_const.prodMk hy)

end FalconerPacking
