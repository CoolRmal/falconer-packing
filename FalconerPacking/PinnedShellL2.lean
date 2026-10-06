/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircleEnergyIntegration
public import FalconerPacking.ScaledFourierBallEnergy

/-!
# The actual joint shell exponent from an explicit circle estimate

This is the integration stage of the shell argument. The packet-chain circle estimate and the
omitted-frequency bound remain explicit hypotheses on actual spectral averages. Joint
measurability, Liu's identity, polar integration, and the source's Fourier/Frostman exponent
are proved in the imported lemmas and assembled here with the exact `2π` convention.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- Integrating a circle estimate with factor `A * R^(c-1)` yields the shell exponent
`1-s+c`. The error is precisely the actual omitted spectral-circle energy. -/
theorem exists_pinned_shell_energy_bound
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] [SFinite ν]
    {s C L lo hi : ℝ} (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (hL : 0 < L) (hlo : 0 ≤ lo) (hhi : 0 < hi) :
    ∃ B > 0, ∀ (R c A : ℝ) (E : ℝ≥0∞), 0 < R → 0 ≤ A →
      ∀ f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ,
      Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
        f p.1 p.2) →
      (∀ᵐ y ∂ν, ∀ x, f y x ≠ 0 → dist x y ≤ L) →
      (∀ᵐ r ∂volume.restrict (Ioo (lo * R) (hi * R)),
        (∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
          ENNReal.ofReal (A * R ^ (c - 1)) * ∫⁻ θ,
            ENNReal.ofReal (‖charFun μ ((-2 * Real.pi) •
              (r • angularDirection θ))‖ ^ 2) ∂radialAngularMeasure) →
      ((∫⁻ r in Ioi (0 : ℝ) \ Ioo (lo * R) (hi * R), ENNReal.ofReal r *
        ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤ E) →
      (∫⁻ p, ENNReal.ofReal (‖complexDistanceDensity (f p.1) p.1 p.2‖ ^ 2)
        ∂ν.prod volume) ≤ ENNReal.ofReal (B * A * R ^ (1 - s + c)) +
          ENNReal.ofReal (L * (2 * Real.pi) ^ 2) * E := by
  let μ' := μ.map (fun x ↦ (-2 * Real.pi) • x)
  haveI : IsProbabilityMeasure μ' := by dsimp [μ']; infer_instance
  obtain ⟨B₀, hB₀, hb⟩ := exists_source_fourier_ball_energy_bound μ hs hs₂ hfr
  let B := L * (2 * Real.pi) ^ 2 * B₀ * hi ^ (2 - s)
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro R c A E hR hA f hf hsupport hcircle htail
  have hcircle' : ∀ᵐ r ∂volume.restrict (Ioo (lo * R) (hi * R)),
      (∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
        ENNReal.ofReal (A * R ^ (c - 1)) * ∫⁻ θ,
          ENNReal.ofReal (‖charFun μ' (r • angularDirection θ)‖ ^ 2)
            ∂radialAngularMeasure := by
    simpa only [μ', charFun_map_smul] using hcircle
  have hbound := lintegral_joint_distance_sq_le_of_circle_band μ' ν f hf hL.le
    (mul_nonneg hlo hR.le) hsupport hcircle' htail
  have hball : (∫⁻ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (hi * R),
      ENNReal.ofReal (‖charFun μ' ξ‖ ^ 2)) ≤
      ENNReal.ofReal (B₀ * (hi * R) ^ (2 - s)) := by
    simpa only [μ', charFun_map_smul] using hb (hi * R) (mul_pos hhi hR)
  apply hbound.trans
  apply le_trans (mul_le_mul_right (add_le_add (mul_le_mul_right hball _) (le_refl E)) _)
  rw [mul_add, ← ENNReal.ofReal_mul (mul_nonneg hA (Real.rpow_nonneg hR.le _)),
    ← ENNReal.ofReal_mul (by positivity)]
  have he : L * (2 * Real.pi) ^ 2 * (A * R ^ (c - 1) * (B₀ * (hi * R) ^ (2 - s))) =
      B * A * R ^ (1 - s + c) := by
    rw [Real.mul_rpow hhi.le hR.le]
    calc
      _ = B * A * (R ^ (c - 1) * R ^ (2 - s)) := by dsimp [B]; ring
      _ = _ := by rw [← Real.rpow_add hR]; congr 2; ring
  rw [he]

end FalconerPacking
