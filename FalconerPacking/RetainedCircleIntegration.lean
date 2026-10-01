/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleEnergyIntegration
import FalconerPacking.TerminalCircleEnergy
import FalconerPacking.ScaledFourierBallEnergy

/-!
# Radial integration with the actual circle-chain factor

The circle-chain estimate contains an inverse radius. Keeping it through polar integration
gives the source Fourier mass times the inverse lower annular radius. A uniform reconstruction
error instead costs only the finite annular area.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- A uniform radial error costs at most the square of the outer radius. -/
theorem lintegral_radial_jacobian_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ r in Ioo a b, ENNReal.ofReal r) ≤ ENNReal.ofReal (b ^ 2) := by
  calc
    _ ≤ ∫⁻ r in Ioo a b, ENNReal.ofReal b := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact ENNReal.ofReal_le_ofReal hr.2.le
    _ = ENNReal.ofReal b * ENNReal.ofReal (b - a) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    _ ≤ ENNReal.ofReal b * ENNReal.ofReal b := by
      gcongr
      linarith
    _ = _ := by rw [← ENNReal.ofReal_mul (ha.trans hab), pow_two]

/-- Actual normalized circle energy with its inverse-radius factor integrates against
planar source energy, plus the explicit finite-area reconstruction error. -/
theorem lintegral_circle_chain_band_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (C : ℝ → ℝ≥0∞) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (A E : ℝ≥0∞)
    (hcircle : ∀ᵐ r ∂volume.restrict (Ioo a b), C r ≤
      A * ENNReal.ofReal (1 / r) *
        (∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
          ∂radialAngularProbability) + E) :
    (∫⁻ r in Ioo a b, ENNReal.ofReal r * C r) ≤
      A * ENNReal.ofReal (1 / a) * (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        (∫⁻ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) b,
          ‖planarMeasureFourier μ ξ‖ₑ ^ 2) + E * ENNReal.ofReal (b ^ 2) := by
  let F := fun ξ ↦ ‖planarMeasureFourier μ ξ‖ₑ ^ 2
  have hF : Measurable F := (continuous_planarMeasureFourier μ).measurable.enorm.pow_const 2
  let S := fun r : ℝ ↦ ∫⁻ θ, F (r • angularDirection θ) ∂radialAngularMeasure
  have hS : Measurable S := by
    apply Measurable.lintegral_prod_right
    exact hF.comp (show Measurable
      (fun p : ℝ × ℝ ↦ p.1 • angularDirection p.2) by fun_prop)
  let D := A * ENNReal.ofReal (1 / a) * (ENNReal.ofReal (2 * Real.pi))⁻¹
  have hp : ∀ᵐ r ∂volume.restrict (Ioo a b), C r ≤ D * S r + E := by
    filter_upwards [hcircle, ae_restrict_mem measurableSet_Ioo] with r hr hrab
    apply hr.trans
    dsimp only [D, S, F]
    rw [radialAngularProbability, lintegral_smul_measure, smul_eq_mul]
    rw [← mul_assoc]
    gcongr
    exact hrab.1.le
  calc
    _ ≤ ∫⁻ r in Ioo a b, D * (ENNReal.ofReal r * S r) + E * ENNReal.ofReal r := by
      apply lintegral_mono_ae
      filter_upwards [hp] with r hr
      simpa only [mul_add, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_right hr
        (ENNReal.ofReal r)
    _ = D * (∫⁻ r in Ioo a b, ENNReal.ofReal r * S r) +
        E * (∫⁻ r in Ioo a b, ENNReal.ofReal r) := by
      rw [lintegral_add_left (by fun_prop),
        lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
    _ ≤ _ := by
      apply add_le_add
      · exact mul_le_mul_right (lintegral_weighted_circle_band_le hF ha.le) D
      · exact mul_le_mul_right (lintegral_radial_jacobian_le ha.le hab) E

/-- The preceding annular integration has the exact Frostman dimensional power.
Its inverse lower radius is retained explicitly. -/
theorem exists_circle_chain_band_frostman_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {s C₀ : ℝ} (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (F : ℝ → ℝ≥0∞) {a b : ℝ},
      0 < a → a ≤ b → ∀ A E : ℝ≥0∞,
      (∀ᵐ r ∂volume.restrict (Ioo a b), F r ≤
        A * ENNReal.ofReal (1 / r) *
          (∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
            ∂radialAngularProbability) + E) →
      (∫⁻ r in Ioo a b, ENNReal.ofReal r * F r) ≤
        A * ENNReal.ofReal (1 / a) * (ENNReal.ofReal (2 * Real.pi))⁻¹ *
          ENNReal.ofReal (C₁ * b ^ (2 - s)) + E * ENNReal.ofReal (b ^ 2) := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_source_fourier_ball_energy_bound μ hs hs₂ hfr
  refine ⟨C₁, hC₁, fun F a b ha hab A E hF ↦ ?_⟩
  apply (lintegral_circle_chain_band_le μ F ha hab A E hF).trans
  apply add_le_add_left
  apply mul_le_mul_right
  simpa only [planarMeasureFourier_eq_charFun, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _)] using hb b (ha.trans_le hab)

end FalconerPacking
