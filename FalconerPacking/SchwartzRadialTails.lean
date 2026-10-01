/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.UniformSchwartzTails

/-!
# Uniform radial tails of Schwartz families

Spatial moments give every inverse power of the radius for the actual first-norm tail.
-/

noncomputable section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace FalconerPacking

/-- The radial first-norm tail is controlled by the actual spatial moment. -/
theorem lintegral_enorm_schwartz_radial_tail_le
    (F : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (m : ℕ) {L : ℝ} (hL : 0 < L) :
    (∫⁻ x in {x | L ≤ ‖x‖}, ‖F x‖ₑ) ≤
      ENNReal.ofReal ((∫ x, ‖x‖ ^ m * ‖F x‖) / L ^ m) := by
  let S := {x : EuclideanSpace ℝ (Fin 2) | L ≤ ‖x‖}
  have hS : MeasurableSet S := isClosed_le continuous_const continuous_norm |>.measurableSet
  have hmono : L ^ m * (∫ x in S, ‖F x‖) ≤ ∫ x, ‖x‖ ^ m * ‖F x‖ := by
    rw [← integral_const_mul]
    apply (setIntegral_mono_on (F.integrable.norm.const_mul _).integrableOn
      (F.integrable_pow_mul volume m).integrableOn hS ?_).trans
      (setIntegral_le_integral (F.integrable_pow_mul volume m) (by
        filter_upwards with x
        positivity))
    intro x hx
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL.le hx m) (norm_nonneg _)
  rw [← ofReal_integral_norm_eq_lintegral_enorm F.integrable.integrableOn]
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ (pow_pos hL m)).mpr (by simpa only [mul_comm] using hmono)

/-- Bounded actual Schwartz families have uniform radial tails at every inverse power. -/
theorem exists_uniform_schwartz_radial_tail {ι : Type*}
    (F : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hF : IsVonNBounded ℝ (range F)) (m : ℕ) :
    ∃ C > 0, ∀ i (L : ℝ), 0 < L →
      (∫⁻ x in {x | L ≤ ‖x‖}, ‖F i x‖ₑ) ≤ ENNReal.ofReal (C / L ^ m) := by
  obtain ⟨C, hC, hc⟩ := exists_uniform_schwartz_moment F hF m
  refine ⟨C, hC, fun i L hL ↦ ?_⟩
  exact (lintegral_enorm_schwartz_radial_tail_le (F i) m hL).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hc i) (pow_nonneg hL.le m)))

end FalconerPacking
