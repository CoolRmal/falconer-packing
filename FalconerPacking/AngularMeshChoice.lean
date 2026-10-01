/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularGridGeometry
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Choosing the concrete angular grid from a physical uncertainty

The integer grid size is the floor of two pi divided by the required uncertainty. Its
actual spacing lies between that uncertainty and twice it; no matching grid is assumed.
-/

noncomputable section

namespace FalconerPacking

/-- Every positive angular uncertainty at most pi has an integer grid of comparable spacing. -/
theorem exists_angular_grid_for_width {w : ℝ} (hw : 0 < w) (hwπ : w ≤ Real.pi) :
    ∃ N : ℕ, 0 < N ∧ w ≤ 2 * Real.pi / N ∧ 2 * Real.pi / N ≤ 2 * w := by
  let N := Nat.floor (2 * Real.pi / w)
  have hratio : 2 ≤ 2 * Real.pi / w := (le_div_iff₀ hw).mpr (by linarith)
  have hN₂ : 2 ≤ N := (Nat.le_floor_iff (by positivity)).mpr hratio
  have hN : 0 < N := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : (N : ℝ) ≤ 2 * Real.pi / w := Nat.floor_le (by positivity)
  have hhi : 2 * Real.pi / w < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨N, hN, (le_div_iff₀ hNreal).mpr ?_, (div_le_iff₀ hNreal).mpr ?_⟩
  · have h := (le_div_iff₀ hw).mp hlo
    nlinarith
  · have h := (div_lt_iff₀ hw).mp hhi
    nlinarith [mul_le_mul_of_nonneg_left hN₁ hw.le]

end FalconerPacking
