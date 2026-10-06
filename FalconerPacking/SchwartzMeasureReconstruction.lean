/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicAnnularKernel
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Smooth frequency reconstruction of finite measures

An actual Schwartz kernel can be convolved with a finite source measure. Its first norm is
controlled by the source mass. The dyadically rescaled low-pass kernels reconstruct the source
against bounded continuous complex tests, by an explicit change of variables and dominated
convergence. No positivity of the kernels or absolute continuity of the source is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal Topology

namespace FalconerPacking

/-- Convolution of a finite source measure with an actual Schwartz kernel. -/
def schwartzMeasureDensity (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℂ := ∫ z, K (x - z) ∂μ

theorem integrable_schwartzMeasureDensity_integrand
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun z ↦ K (x - z)) μ :=
  (integrable_const (SchwartzMap.seminorm ℝ 0 0 K)).mono'
    (K.continuous.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun _ ↦ K.norm_le_seminorm ℝ _)

/-- Joint integrability needed for actual, rather than distributional, Fubini identities. -/
theorem integrable_schwartzMeasureDensity_prod
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      K (p.1 - p.2)) (volume.prod μ) := by
  simpa using (integrable_const (1 : ℂ) (μ := μ)).convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) K.integrable

theorem integrable_schwartzMeasureDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Integrable (schwartzMeasureDensity μ K) volume :=
  (integrable_schwartzMeasureDensity_prod μ K).integral_prod_left

/-- The first norm of a whole smoothed source is bounded by source mass times kernel first norm. -/
theorem integral_norm_schwartzMeasureDensity_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫ x, ‖schwartzMeasureDensity μ K x‖) ≤ μ.real univ * ∫ x, ‖K x‖ := by
  calc
    _ ≤ ∫ x, ∫ z, ‖K (x - z)‖ ∂μ ∂volume := by
      apply integral_mono (integrable_schwartzMeasureDensity μ K).norm
        (integrable_schwartzMeasureDensity_prod μ K).norm.integral_prod_left
      exact fun _ ↦ norm_integral_le_integral_norm _
    _ = ∫ z, ∫ x, ‖K (x - z)‖ ∂volume ∂μ :=
      integral_integral_swap (integrable_schwartzMeasureDensity_prod μ K).norm
    _ = _ := by
      simp_rw [integral_sub_right_eq_self (fun x ↦ ‖K x‖)]
      simp [smul_eq_mul]

/-- The exact complex test-integral formula for the convolved source. -/
theorem integral_schwartzMeasureDensity_mul_test
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫ x, schwartzMeasureDensity μ K x * g x) =
      ∫ z, ∫ x, K (x - z) * g x ∂volume ∂μ := by
  have hi : Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      K (p.1 - p.2) * g p.1) (volume.prod μ) :=
    (integrable_schwartzMeasureDensity_prod μ K).mul_bdd
      (g.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ g.norm_coe_le_norm p.1)
  calc
    _ = ∫ x, ∫ z, K (x - z) * g x ∂μ ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_mul_const _ _).symm
    _ = _ := integral_integral_swap hi

/-- The exact dilation identity that makes the approximate-identity limit elementary. -/
theorem integral_lowpassSchwartzKernel_mul_test (a : ℝ) (ha : 0 < a)
    (z : EuclideanSpace ℝ (Fin 2)) (g : EuclideanSpace ℝ (Fin 2) → ℂ) :
    (∫ x, lowpassSchwartzKernel a ha (x - z) * g x) =
      ∫ w, unitReproducingKernel w * g (z + a⁻¹ • w) := by
  let f (w : EuclideanSpace ℝ (Fin 2)) :=
    unitReproducingKernel w * g (z + a⁻¹ • w)
  calc
    _ = ∫ x, lowpassSchwartzKernel a ha x * g (z + x) := by
      simpa only [add_sub_cancel_left] using
        (integral_add_left_eq_self
          (fun x ↦ lowpassSchwartzKernel a ha (x - z) * g x) z).symm
    _ = a ^ 2 • ∫ x, f (a • x) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [lowpassSchwartzKernel_apply, f, smul_smul, inv_mul_cancel₀ ha.ne',
        one_smul, smul_mul_assoc]
    _ = a ^ 2 • (|(a ^ 2)⁻¹| • ∫ w, f w) := by
      rw [Measure.integral_comp_smul volume]
      simp only [finrank_euclideanSpace, Fintype.card_fin]
    _ = _ := by
      rw [smul_smul, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_smul]

/-- Low-pass reconstruction against every bounded continuous complex test. -/
theorem tendsto_integral_lowpassMeasureDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hatop : Tendsto a atTop atTop)
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Tendsto (fun n ↦ ∫ x, schwartzMeasureDensity μ (lowpassSchwartzKernel (a n) (ha n)) x * g x)
      atTop (𝓝 (∫ z, g z ∂μ)) := by
  have hK : (∫ w, unitReproducingKernel w) = 1 := by
    simpa [lowpassSchwartzKernel_apply] using integral_lowpassSchwartzKernel 1 (by norm_num)
  have hinv : Tendsto (fun n ↦ (a n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hatop
  have hpoint (z : EuclideanSpace ℝ (Fin 2)) :
      Tendsto (fun n ↦ ∫ w, unitReproducingKernel w * g (z + (a n)⁻¹ • w))
        atTop (𝓝 (g z)) := by
    have h := tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun n w ↦ unitReproducingKernel w * g (z + (a n)⁻¹ • w))
      (f := fun w ↦ unitReproducingKernel w * g z)
      (fun w ↦ ‖unitReproducingKernel w‖ * ‖g‖)
      (fun n ↦ (show Continuous (fun w ↦ unitReproducingKernel w *
        g (z + (a n)⁻¹ • w)) by fun_prop).aestronglyMeasurable)
      (unitReproducingKernel.integrable.norm.mul_const ‖g‖)
      (fun n ↦ Eventually.of_forall fun w ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _))
      (Eventually.of_forall fun w ↦ tendsto_const_nhds.mul
        ((g.continuous.tendsto z).comp (by
          simpa using tendsto_const_nhds.add (hinv.smul_const w))))
    simpa only [integral_mul_const, hK, one_mul] using h
  have hbound (n : ℕ) (z : EuclideanSpace ℝ (Fin 2)) :
      ‖∫ w, unitReproducingKernel w * g (z + (a n)⁻¹ • w)‖ ≤
        (∫ w, ‖unitReproducingKernel w‖) * ‖g‖ := by
    simpa only [integral_mul_const] using norm_integral_le_of_norm_le
      (unitReproducingKernel.integrable.norm.mul_const ‖g‖)
      (Eventually.of_forall fun w ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _))
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n z ↦ ∫ w, unitReproducingKernel w * g (z + (a n)⁻¹ • w))
    (f := fun z ↦ g z)
    (fun _ ↦ (∫ w, ‖unitReproducingKernel w‖) * ‖g‖)
    (fun n ↦ (show Continuous (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 2) ↦ unitReproducingKernel p.2 *
        g (p.1 + (a n)⁻¹ • p.2)) by
          fun_prop).stronglyMeasurable.integral_prod_right.aestronglyMeasurable)
    (integrable_const _) (fun n ↦ Eventually.of_forall (hbound n))
    (Eventually.of_forall hpoint)
  convert h using 1
  funext n
  rw [integral_schwartzMeasureDensity_mul_test]
  simp_rw [integral_lowpassSchwartzKernel_mul_test]

end FalconerPacking
