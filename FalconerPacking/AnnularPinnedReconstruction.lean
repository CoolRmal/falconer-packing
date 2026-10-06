/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CompactAnnularReconstruction
public import FalconerPacking.ComplexDistancePushforward
public import FalconerPacking.PinnedKernel

/-!
# Joint pinned reconstruction of actual annular source pieces

The compact smooth source expansion reconstructs the actual joint pin-distance law after
pushing every complex annular piece through the distance map. This supplies the test
reconstruction hypothesis in the annular density-limit theorem without assuming it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerPacking

/-- The circle density is jointly measurable in the pin and the distance variable. -/
theorem measurable_joint_complexDistanceDensity
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦ complexDistanceDensity f p.1 p.2) := by
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      ∫ θ, f (p.2 • angularDirection θ + p.1) ∂radialAngularMeasure) := by
    have hh : Measurable (fun q : (EuclideanSpace ℝ (Fin 2) × ℝ) × ℝ ↦
        f (q.1.2 • angularDirection q.2 + q.1.1)) := by fun_prop
    exact hh.stronglyMeasurable.integral_prod_right.measurable
  unfold complexDistanceDensity pinnedCircularAverage circularAverage
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd) <;> fun_prop

/-- An integrable complex source gives an integrable joint density for every finite pin measure. -/
theorem integrable_joint_complexDistanceDensity
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) (hi : Integrable f volume) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦ complexDistanceDensity f p.1 p.2)
      (ν.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦ complexDistanceDensity f p.1 p.2)
      (ν.prod volume) := (measurable_joint_complexDistanceDensity hf).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨Eventually.of_forall (integrable_complexDistanceDensity hf hi), ?_⟩
  apply (integrable_const (∫ x, ‖f x‖) (μ := ν)).mono'
    hm.norm.integral_prod_right'
  filter_upwards with y
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  exact integral_norm_complexDistanceDensity_le hf hi y

/-- Finite complex source sums may be pushed forward term by term against joint tests. -/
theorem integral_sum_complexDistanceDensity_mul_joint_test
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (f : ℕ → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (N : ℕ)
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2) × ℝ) ℂ) :
    (∫ p, (∑ n ∈ Finset.range N, complexDistanceDensity (f n) p.1 p.2) * g p ∂ν.prod volume) =
      ∫ y, ∫ x, (∑ n ∈ Finset.range N, f n x) * g (y, dist x y) ∂volume ∂ν := by
  have hi (n : ℕ) : Integrable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      complexDistanceDensity (f n) p.1 p.2 * g p) (ν.prod volume) :=
    (integrable_joint_complexDistanceDensity ν (f n).continuous.measurable
      (f n).integrable).mul_bdd g.continuous.aestronglyMeasurable
      (Eventually.of_forall g.norm_coe_le_norm)
  have hprod : Integrable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      (∑ n ∈ Finset.range N, complexDistanceDensity (f n) p.1 p.2) * g p) (ν.prod volume) := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ (fun n _ ↦ hi n)
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards with y
  have hg : Measurable (fun t : ℝ ↦ g (y, t)) := by fun_prop
  have hbound (t : ℝ) : ‖g (y, t)‖ ≤ ‖g‖ := g.norm_coe_le_norm _
  have htest (n : ℕ) := complexDistanceDensity_test_integrable
    (f n).continuous.measurable (f n).integrable y hg hbound
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun n _ ↦ (htest n).1),
    integral_finsetSum _ (fun n _ ↦ (htest n).2)]
  exact Finset.sum_congr rfl fun n _ ↦ integral_complexDistanceDensity_mul_test
    (f n).continuous.measurable (f n).integrable y hg hbound

/-- The actual annular circle densities reconstruct the joint pin-distance law. The only
geometric source hypothesis is bounded support; the pin measure is any fixed finite measure. -/
theorem tendsto_joint_compactAnnularSource_distanceDensity
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχone : ∀ᵐ x ∂μ, χ x = 1) (hχnorm : ∀ x, ‖χ x‖ ≤ 1)
    {T : ℕ} (hT : 0 < T)
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2) × ℝ) ℂ) :
    Tendsto (fun N ↦ ∫ p, (∑ n ∈ Finset.range N,
      complexDistanceDensity (compactAnnularSource μ hμ χ hχ T n) p.1 p.2) * g p ∂ν.prod volume)
      atTop (𝓝 (∫ p, g p ∂jointPinnedDistanceMeasure μ ν)) := by
  let f := compactAnnularSource μ hμ χ hχ T
  let C := μ.real univ * (∫ w, ‖unitReproducingKernel w‖) * ‖g‖
  have hpoint (y : EuclideanSpace ℝ (Fin 2)) :
      Tendsto (fun N ↦ ∫ x, (∑ n ∈ Finset.range (N + 1), f n x) * g (y, dist x y))
        atTop (𝓝 (∫ x, g (y, dist x y) ∂μ)) := by
    let ψ := g.compContinuous ⟨fun x ↦ (y, dist x y), by fun_prop⟩
    exact (tendsto_add_atTop_iff_nat 1).mpr
      (tendsto_integral_compactAnnularSource μ hμ χ hχ hχone hT ψ)
  have hbound (N : ℕ) (y : EuclideanSpace ℝ (Fin 2)) :
      ‖∫ x, (∑ n ∈ Finset.range (N + 1), f n x) * g (y, dist x y)‖ ≤ C := by
    let K := lowpassSchwartzKernel (2 ^ (T * N)) (by positivity)
    have hi := (integrable_schwartzMeasureDensity μ K).norm.mul_const ‖g‖
    calc
      _ ≤ ∫ x, ‖schwartzMeasureDensity μ K x‖ * ‖g‖ := by
        apply norm_integral_le_of_norm_le hi
        filter_upwards with x
        rw [show (∑ n ∈ Finset.range (N + 1), f n x) =
          χ x * schwartzMeasureDensity μ K x from sum_compactAnnularSource μ hμ χ hχ T N x]
        rw [norm_mul, norm_mul]
        exact mul_le_mul
          (mul_le_of_le_one_left (norm_nonneg _) (hχnorm x))
          (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
      _ ≤ (μ.real univ * ∫ x, ‖K x‖) * ‖g‖ := by
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right (integral_norm_schwartzMeasureDensity_le μ K)
          (norm_nonneg g)
      _ = C := by rw [integral_norm_lowpassSchwartzKernel]
  have hlim := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun N y ↦ ∫ x, (∑ n ∈ Finset.range (N + 1), f n x) * g (y, dist x y))
    (f := fun y ↦ ∫ x, g (y, dist x y) ∂μ) (fun _ ↦ C)
    (fun N ↦ (show Continuous (fun p : EuclideanSpace ℝ (Fin 2) ×
        EuclideanSpace ℝ (Fin 2) ↦
        (∑ n ∈ Finset.range (N + 1), f n p.2) * g (p.1, dist p.2 p.1)) by
      apply Continuous.mul
      · simpa only [Function.comp_def, sum_apply] using
          (∑ n ∈ Finset.range (N + 1), f n).continuous.comp continuous_snd
      · fun_prop).stronglyMeasurable.integral_prod_right.aestronglyMeasurable)
    (integrable_const _) (fun N ↦ Eventually.of_forall (hbound N))
    (Eventually.of_forall hpoint)
  have htarget : (∫ y, ∫ x, g (y, dist x y) ∂μ ∂ν) =
      ∫ p, g p ∂jointPinnedDistanceMeasure μ ν := by
    rw [jointPinnedDistanceMeasure, integral_map (by fun_prop)
      g.continuous.aestronglyMeasurable]
    symm
    apply integral_prod
    exact (integrable_const ‖g‖).mono' (by fun_prop)
      (Eventually.of_forall fun p ↦ g.norm_coe_le_norm _)
  rw [htarget] at hlim
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert hlim using 1
  funext N
  exact integral_sum_complexDistanceDensity_mul_joint_test ν f (N + 1) g

end FalconerPacking
