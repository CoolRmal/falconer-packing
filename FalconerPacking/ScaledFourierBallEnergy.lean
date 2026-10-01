/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PolarFourierEnergy

/-!
# Fourier ball bounds with the actual frequency normalization

The `2π` source Fourier convention is a fixed dilation of the characteristic function.
Expanding the source preserves a Frostman bound, which allows the previously proved Gaussian
estimate to be used without silently changing Fourier conventions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- A spatial dilation of magnitude at least one preserves the Frostman exponent. -/
theorem IsFrostman.map_expanding_smul {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    {s C κ : ℝ} (hfr : IsFrostman μ s C) (hs : 0 ≤ s) (hκ : 1 ≤ |κ|) :
    IsFrostman (μ.map (fun x ↦ κ • x)) s (max C 1) := by
  have hkpos : 0 < |κ| := lt_of_lt_of_le zero_lt_one hκ
  have hk : κ ≠ 0 := abs_pos.mp hkpos
  intro y r hr hr₁
  rw [Measure.map_apply (by fun_prop) Metric.isOpen_ball.measurableSet]
  have he : (fun x : EuclideanSpace ℝ (Fin 2) ↦ κ • x) ⁻¹' Metric.ball y r =
      Metric.ball (κ⁻¹ • y) (r / |κ|) := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm]
    have hx : κ • x - y = κ • (x - κ⁻¹ • y) := by simp [smul_sub, smul_smul, hk]
    rw [hx, norm_smul, Real.norm_eq_abs]
    rw [mul_comm]
    exact (lt_div_iff₀ hkpos).symm
  rw [he]
  have hrr : r / |κ| ≤ r := div_le_self hr.le hκ
  apply (hfr _ _ (div_pos hr hkpos) (hrr.trans hr₁)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    C * (r / |κ|) ^ s ≤ max C 1 * (r / |κ|) ^ s :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    _ ≤ max C 1 * r ^ s := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hrr hs) (le_trans zero_le_one (le_max_right _ _))

/-- The actual dilated characteristic function obeys one uniform Fourier ball bound. -/
theorem exists_scaled_fourier_ball_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {s C κ : ℝ} (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (hκ : 1 ≤ |κ|) : ∃ B > 0, ∀ R : ℝ, 0 < R →
      (∫⁻ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
        ENNReal.ofReal (‖charFun μ (κ • ξ)‖ ^ 2)) ≤ ENNReal.ofReal (B * R ^ (2 - s)) := by
  let μ' := μ.map (fun x ↦ κ • x)
  haveI : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨B, hB, hb⟩ := exists_fourier_ball_energy_bound μ' hs hs₂
    (hfr.map_expanding_smul hs hκ)
  refine ⟨B, hB, fun R hR ↦ ?_⟩
  have hi := integrableOn_charFun_norm_sq_ball μ' R
  have he := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ sq_nonneg _)
  have hbound := ENNReal.ofReal_le_ofReal (hb R hR)
  rw [he] at hbound
  simpa only [μ', charFun_map_smul] using hbound

/-- The source's literal `2π` Fourier convention is covered by the Gaussian estimate. -/
theorem exists_source_fourier_ball_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {s C : ℝ} (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B > 0, ∀ R : ℝ, 0 < R →
      (∫⁻ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
        ENNReal.ofReal (‖charFun μ ((-2 * Real.pi) • ξ)‖ ^ 2)) ≤
          ENNReal.ofReal (B * R ^ (2 - s)) := by
  apply exists_scaled_fourier_ball_energy_bound μ hs hs₂ hfr
  rw [abs_of_neg (by nlinarith [Real.pi_pos])]
  nlinarith [Real.two_le_pi]

end FalconerPacking
