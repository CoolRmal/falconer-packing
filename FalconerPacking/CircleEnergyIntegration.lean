/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.JointPinnedCircleEnergy

/-!
# Integrating an explicit circle-energy estimate

These assembly results take the actual integrated circle inequality as a hypothesis. They do
not assert the packet or chain estimate that will supply that hypothesis. Polar coordinates
and the checked Gaussian Fourier bound supply the radial weights and the Frostman exponent.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- The radial Jacobian converts an annular circle-energy integral to planar Fourier mass. -/
theorem lintegral_weighted_circle_band_le {F : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hF : Measurable F) {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ r in Ioo a b, ENNReal.ofReal r *
      ∫⁻ θ, F (r • angularDirection θ) ∂radialAngularMeasure) ≤
      ∫⁻ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) b, F ξ := by
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) b
  let S := Ioo a b ×ˢ Ioo (-Real.pi) Real.pi
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  calc
    _ = ∫⁻ p : ℝ × ℝ in S, ENNReal.ofReal p.1 * F (p.1 • angularDirection p.2) := by
      rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro r
      rw [radialAngularMeasure, ← setLIntegral_congr Ioo_ae_eq_Ioc,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ p : ℝ × ℝ in S,
        ENNReal.ofReal p.1 * B.indicator F (p.1 • angularDirection p.2) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS] with p hp
      have hpB : p.1 • angularDirection p.2 ∈ B := by
        simpa only [B, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          norm_angularDirection, mul_one, abs_of_pos (ha.trans_lt hp.1.1)] using hp.1.2
      rw [indicator_of_mem hpB]
    _ ≤ ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * B.indicator F (p.1 • angularDirection p.2) :=
      lintegral_mono_set (fun p hp ↦ ⟨ha.trans_lt hp.1.1, hp.2⟩)
    _ = _ := by
      rw [lintegral_polar_euclidean, lintegral_indicator Metric.isOpen_ball.measurableSet]

/-- On the main radial band, an actual circle estimate integrates with exactly one factor
of the source's planar Fourier mass. -/
theorem lintegral_circle_band_le_source_ball
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {a b A : ℝ} (ha : 0 ≤ a)
    (hcircle : ∀ᵐ r ∂volume.restrict (Ioo a b),
      (∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
        ENNReal.ofReal A * ∫⁻ θ,
          ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) ∂radialAngularMeasure) :
    (∫⁻ r in Ioo a b, ENNReal.ofReal r *
      ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
      ENNReal.ofReal A *
        ∫⁻ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) b,
          ENNReal.ofReal (‖charFun μ ξ‖ ^ 2) := by
  calc
    _ ≤ ∫⁻ r in Ioo a b, ENNReal.ofReal r * (ENNReal.ofReal A *
        ∫⁻ θ, ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2)
          ∂radialAngularMeasure) := by
      apply lintegral_mono_ae
      filter_upwards [hcircle] with r hr
      exact mul_le_mul_right hr _
    _ = ENNReal.ofReal A * (∫⁻ r in Ioo a b, ENNReal.ofReal r *
        ∫⁻ θ, ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2)
          ∂radialAngularMeasure) := by
      simp_rw [mul_left_comm _ (ENNReal.ofReal A)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (lintegral_weighted_circle_band_le
      (F := fun ξ ↦ ENNReal.ofReal (‖charFun μ ξ‖ ^ 2)) (by fun_prop) ha) _

/-- A scalar integrated annular estimate is sufficient; no pointwise comparison to the source
circle is required. This form applies after arbitrary pin-dependent packet selections. -/
theorem lintegral_joint_distance_sq_le_of_annular_energy
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hf : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      f p.1 p.2)) {L a b : ℝ} {M E : ℝ≥0∞} (hL₀ : 0 ≤ L) (ha : 0 ≤ a)
    (hL : ∀ᵐ y ∂ν, ∀ x, f y x ≠ 0 → dist x y ≤ L)
    (hmain : (∫⁻ r in Ioo a b, ENNReal.ofReal r *
      ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤ M)
    (htail : (∫⁻ r in Ioi (0 : ℝ) \ Ioo a b, ENNReal.ofReal r *
      ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤ E) :
    (∫⁻ p, ENNReal.ofReal (‖complexDistanceDensity (f p.1) p.1 p.2‖ ^ 2)
      ∂ν.prod volume) ≤ ENNReal.ofReal (L * (2 * Real.pi) ^ 2) * (M + E) := by
  apply (lintegral_joint_complexDistanceDensity_sq_le ν f hf hL₀ hL).trans
  apply mul_le_mul_right
  have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun r hr ↦ ha.trans_lt hr.1
  rw [← lintegral_inter_add_sdiff _ (Ioi (0 : ℝ)) measurableSet_Ioo,
    inter_eq_right.mpr hsub]
  exact add_le_add hmain htail

/-- An actual circle bound on a main annulus plus the actual omitted spectral energy controls
all of the joint distance-density energy. No packet estimate is assumed implicitly. -/
theorem lintegral_joint_distance_sq_le_of_circle_band
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [SFinite ν]
    (f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hf : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      f p.1 p.2)) {L a b A : ℝ} {E : ℝ≥0∞} (hL₀ : 0 ≤ L) (ha : 0 ≤ a)
    (hL : ∀ᵐ y ∂ν, ∀ x, f y x ≠ 0 → dist x y ≤ L)
    (hcircle : ∀ᵐ r ∂volume.restrict (Ioo a b),
      (∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
        ENNReal.ofReal A * ∫⁻ θ,
          ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) ∂radialAngularMeasure)
    (htail : (∫⁻ r in Ioi (0 : ℝ) \ Ioo a b, ENNReal.ofReal r *
      ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤ E) :
    (∫⁻ p, ENNReal.ofReal (‖complexDistanceDensity (f p.1) p.1 p.2‖ ^ 2)
      ∂ν.prod volume) ≤ ENNReal.ofReal (L * (2 * Real.pi) ^ 2) *
        (ENNReal.ofReal A * (∫⁻ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) b,
          ENNReal.ofReal (‖charFun μ ξ‖ ^ 2)) + E) := by
  exact lintegral_joint_distance_sq_le_of_annular_energy ν f hf hL₀ ha hL
    (lintegral_circle_band_le_source_ball μ ν f ha hcircle) htail

/-- The checked Gaussian Fourier estimate supplies the source ball term in nonnegative form. -/
theorem exists_lintegral_fourier_ball_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B > 0, ∀ R : ℝ, 0 < R →
      (∫⁻ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
        ENNReal.ofReal (‖charFun μ ξ‖ ^ 2)) ≤ ENNReal.ofReal (B * R ^ (2 - s)) := by
  obtain ⟨B, hB, hb⟩ := exists_fourier_ball_energy_bound μ hs hs₂ hfr
  refine ⟨B, hB, fun R hR ↦ ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_charFun_norm_sq_ball μ R)
    (ae_of_all _ fun _ ↦ sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hb R hR)

end FalconerPacking
