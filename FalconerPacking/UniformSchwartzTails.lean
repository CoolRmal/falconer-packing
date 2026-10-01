/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.UniformSchwartzFourier

/-!
# Uniform transverse tails of actual Schwartz kernels

Weighted first moments control the integral outside any transverse strip. The constants
are uniform over a bounded Schwartz family and all normals of norm at most one.
-/

noncomputable section

open MeasureTheory Set Bornology FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The actual first-norm transverse tail is controlled by a spatial moment. -/
theorem lintegral_enorm_schwartz_transverse_tail_le
    (F : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (m : ℕ)
    (e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ ≤ 1) {L : ℝ} (hL : 0 < L) :
    (∫⁻ x in {x | L ≤ |⟪e, x⟫|}, ‖F x‖ₑ) ≤
      ENNReal.ofReal ((∫ x, ‖x‖ ^ m * ‖F x‖) / L ^ m) := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) := {x | L ≤ |⟪e, x⟫|}
  have hS : MeasurableSet S := isClosed_le continuous_const (by fun_prop) |>.measurableSet
  have hmono : L ^ m * (∫ x in S, ‖F x‖) ≤ ∫ x, ‖x‖ ^ m * ‖F x‖ := by
    rw [← integral_const_mul]
    apply (setIntegral_mono_on (F.integrable.norm.const_mul _).integrableOn
      (F.integrable_pow_mul volume m).integrableOn hS ?_).trans
      (setIntegral_le_integral (F.integrable_pow_mul volume m) (by
        filter_upwards with x
        exact mul_nonneg (pow_nonneg (norm_nonneg x) m) (norm_nonneg (F x))))
    intro x hx
    have ht : |⟪e, x⟫| ≤ ‖x‖ :=
      (abs_real_inner_le_norm e x).trans
        ((mul_le_mul_of_nonneg_right he (norm_nonneg x)).trans_eq (one_mul _))
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL.le (hx.trans ht) m) (norm_nonneg _)
  rw [← ofReal_integral_norm_eq_lintegral_enorm F.integrable.integrableOn]
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ (pow_pos hL m)).mpr (by simpa only [mul_comm] using hmono)

/-- Bounded Schwartz families have uniform first norms. -/
theorem exists_uniform_schwartz_lintegral_enorm {ι : Type*}
    (F : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hF : IsVonNBounded ℝ (range F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, (∫⁻ x, ‖F i x‖ₑ) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hc⟩ := exists_uniform_schwartz_moment F hF 0
  refine ⟨C, hC, fun i ↦ ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm (F i).integrable]
  apply ENNReal.ofReal_le_ofReal
  simpa only [pow_zero, one_mul] using hc i

/-- Every prescribed power of decay is available for all actual transverse tails. -/
theorem exists_uniform_schwartz_transverse_tail {ι : Type*}
    (F : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hF : IsVonNBounded ℝ (range F)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i (e : EuclideanSpace ℝ (Fin 2)), ‖e‖ ≤ 1 →
      ∀ L : ℝ, 0 < L → (∫⁻ x in {x | L ≤ |⟪e, x⟫|}, ‖F i x‖ₑ) ≤
        ENNReal.ofReal (C / L ^ m) := by
  obtain ⟨C, hC, hc⟩ := exists_uniform_schwartz_moment F hF m
  refine ⟨C, hC, fun i e he L hL ↦ ?_⟩
  exact (lintegral_enorm_schwartz_transverse_tail_le (F i) m e he hL).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hc i) (pow_nonneg hL.le m)))

end FalconerPacking
