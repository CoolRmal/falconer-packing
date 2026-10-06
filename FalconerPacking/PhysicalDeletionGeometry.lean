/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PhysicalChainScales
public import FalconerPacking.PhysicalConditionalDeletion

/-!
# Geometric uncertainty in the actual conditional deletion estimate

The enlarged source-strip width is a fixed geometric factor times the original spatial
ratio. Its three contributions are the parent grid width, the standard-packet uncertainty,
and the mismatch of the effective normal.
-/

@[expose] public section

noncomputable section

namespace FalconerPacking

/-- Standard packet width and effective angular width give the required pair uncertainty. -/
theorem physical_pair_uncertainty_le {w C D L ρ α : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hw : w ≤ L * ρ) (hα : α ≤ ρ) :
    2 * w + C * w + 2 * Real.pi * α * D ≤
      ((2 + C) * L + 2 * Real.pi * D) * ρ := by
  have hw' := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ 2 + C)
  have hα' := mul_le_mul_of_nonneg_right hα (by positivity : 0 ≤ 2 * Real.pi * D)
  nlinarith

/-- The complete coarsened angular uncertainty is bounded by a geometric factor times rho. -/
theorem enlarged_grid_angular_uncertainty_le
    {R δ b Λ ρ L C D ε : ℝ} {M Z : ℕ}
    (hR : 0 ≤ R) (hb₁ : b ≤ 1) (hΛ : 0 ≤ Λ) (hρ : 0 ≤ ρ)
    (hmesh : (M : ℝ)⁻¹ = ρ)
    (hε : ε ≤ ((2 + C) * L + 2 * Real.pi * D) * ρ) :
    8 * R * (((Z : ℝ) + 1) * ((Λ * b) / M) + 2 * ε + D / M) / δ ^ 2 ≤
      (8 * R / δ ^ 2 *
        (((Z : ℝ) + 1) * Λ + 2 * (2 + C) * L + (4 * Real.pi + 1) * D)) * ρ := by
  have hb : Λ * b * ρ ≤ Λ * ρ := by
    have h := mul_le_mul_of_nonneg_left hb₁ (mul_nonneg hΛ hρ)
    nlinarith
  have hz : 0 ≤ (Z : ℝ) + 1 := by positivity
  have hinner : ((Z : ℝ) + 1) * ((Λ * b) / M) + 2 * ε + D / M ≤
      (((Z : ℝ) + 1) * Λ + 2 * (2 + C) * L + (4 * Real.pi + 1) * D) * ρ := by
    simp only [div_eq_mul_inv, hmesh]
    have h := mul_le_mul_of_nonneg_left hb hz
    nlinarith
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 8 * R)) (sq_nonneg δ)
  calc
    _ ≤ 8 * R *
        ((((Z : ℝ) + 1) * Λ + 2 * (2 + C) * L + (4 * Real.pi + 1) * D) * ρ) / δ ^ 2 := h
    _ = _ := by ring

/-- With a dyadic slope grid, the parent enlargement has precisely the required inverse mesh. -/
theorem inv_dyadic_grid_eq_ratio {m n : ℕ} (hmn : m ≤ n) :
    ((2 : ℕ) ^ (n - m) : ℝ)⁻¹ = ((2 : ℝ) ^ n)⁻¹ / ((2 : ℝ) ^ m)⁻¹ := by
  have h := enlarged_dyadic_grid_scale hmn (1 : ℝ)
  simp only [one_mul] at h
  apply (mul_left_cancel₀ (by positivity : ((2 : ℝ) ^ m)⁻¹ ≠ 0))
  rw [← div_eq_mul_inv, h]
  field_simp

end FalconerPacking
