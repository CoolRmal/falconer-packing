/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AngularMeshChoice
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Choosing the source-heavy angular mesh below a conditional threshold

If the pin threshold exceeds the geometric enlargement factor, every nontrivial bad test
has sufficiently small angular uncertainty. The spatial ratio cancels exactly from the
source-mass versus pin-threshold ratio.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace FalconerPacking

/-- The actual angular spacing is chosen from the spatial ratio and geometric factor. -/
theorem exists_angular_grid_below_conditional_threshold {ρ G : ℝ} (hρ : 0 < ρ)
    (hG : 0 < G) {H : ℝ≥0∞} (hHG : ENNReal.ofReal G ≤ H)
    (hsmall : H * ENNReal.ofReal ρ < 1) :
    ∃ N : ℕ, 0 < N ∧ G * ρ ≤ 2 * Real.pi / N ∧ 2 * Real.pi / N ≤ 2 * (G * ρ) := by
  have hreal : G * ρ < 1 := by
    apply ENNReal.ofReal_lt_one.mp
    rw [ENNReal.ofReal_mul hG.le]
    exact (mul_le_mul' hHG le_rfl).trans_lt hsmall
  apply exists_angular_grid_for_width (mul_pos hG hρ)
  exact hreal.le.trans (by linarith [Real.pi_gt_three])

/-- The ratio in the actual source-heavy deletion estimate cancels its spatial scale. -/
theorem angular_source_mass_div_threshold_le {ρ G step : ℝ}
    (hρ : 0 < ρ) (hG : 0 ≤ G) (hstep : step ≤ 2 * (G * ρ)) (A H : ℝ≥0∞) :
    ((2 * A) * ENNReal.ofReal (3 * step)) / (H * ENNReal.ofReal ρ) ≤
      12 * ENNReal.ofReal G * (A / H) := by
  calc
    _ ≤ ((2 * A) * ENNReal.ofReal (6 * G * ρ)) / (H * ENNReal.ofReal ρ) := by
      apply ENNReal.div_le_div_right
      apply mul_le_mul' le_rfl
      exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = (12 * ENNReal.ofReal G * A * ENNReal.ofReal ρ) /
        (H * ENNReal.ofReal ρ) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 6 * G),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat]
      congr 1
      ring
    _ = 12 * ENNReal.ofReal G * (A / H) := by
      rw [ENNReal.mul_div_mul_right _ _ (ENNReal.ofReal_pos.mpr hρ).ne'
        ENNReal.ofReal_ne_top]
      simp only [div_eq_mul_inv, mul_assoc]

end FalconerPacking
