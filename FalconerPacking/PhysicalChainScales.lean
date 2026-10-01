/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.MarkedCircleParentEdge
import FalconerPacking.EnlargedTruncatedEnergy

/-!
# Physical scales and effective angular uncertainty

The curvature condition and the bounded parent scale imply that both the standard angular
width and the chosen coarse width are no larger than the spatial scale ratio. The finite
slope grid uses their literal dyadic ratio, so its energy has exactly the enlarged scales.
-/

noncomputable section

namespace FalconerPacking

/-- Curvature and a parent scale at most one control the standard angular width. -/
theorem standard_angle_le_spatial_ratio {R a b S : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hcurv : b ≤ R * a ^ 2) (hS : Real.sqrt R ≤ S) :
    S⁻¹ ≤ a / b := by
  have hsqrt : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hS₀ : 0 < S := hsqrt.trans_le hS
  have hsq : b ^ 2 ≤ (a * Real.sqrt R) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR.le]
    nlinarith
  have hroot : b ≤ a * Real.sqrt R :=
    (sq_le_sq₀ hb.le (mul_nonneg ha.le hsqrt.le)).mp hsq
  apply (inv_le_inv₀ hS₀ hsqrt).mpr hS |>.trans
  rw [inv_eq_one_div, div_le_div_iff₀ hsqrt hb]
  simpa only [one_mul] using hroot

/-- The actual selected coarse angular scale satisfies the same spatial ratio bound. -/
theorem coarse_angle_le_spatial_ratio {R a b F : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hcurv : b ≤ R * a ^ 2) (hF : R * a ≤ F) :
    F⁻¹ ≤ a / b := by
  have hF₀ : 0 < F := (mul_pos hR ha).trans_le hF
  rw [inv_eq_one_div, div_le_div_iff₀ hF₀ hb, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hF ha.le]

/-- Every actual effective dyadic normal has angular uncertainty at most the spatial ratio. -/
theorem effective_dyadic_angle_le_spatial_ratio {R a b : ℝ} (s e : ℕ)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hcurv : b ≤ R * a ^ 2) (hS : Real.sqrt R ≤ (2 : ℝ) ^ s)
    (hF : R * a ≤ (2 : ℝ) ^ e) :
    ((2 : ℝ) ^ min s e)⁻¹ ≤ a / b := by
  rcases le_total s e with h | h
  · rw [min_eq_left h]
    exact standard_angle_le_spatial_ratio hR ha hb hb₁ hcurv hS
  · rw [min_eq_right h]
    exact coarse_angle_le_spatial_ratio hR ha hb hcurv hF

/-- The exact dyadic parent ratio fixes the integer slope-grid cardinality. -/
theorem enlarged_dyadic_grid_scale {m n : ℕ} (hmn : m ≤ n) (Λ : ℝ) :
    (Λ * ((2 : ℝ) ^ m)⁻¹) / ((2 : ℕ) ^ (n - m) : ℝ) = Λ * ((2 : ℝ) ^ n)⁻¹ := by
  rw [Nat.cast_ofNat, div_eq_mul_inv, mul_assoc, ← mul_inv,
    ← pow_add, Nat.add_sub_of_le hmn]

/-- The finite-grid truncated energy is exactly at the two enlarged original dyadic scales. -/
theorem truncEnergy_enlarged_dyadic_grid_le
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2)))
    {m n : ℕ} (hmn : m ≤ n) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    truncEnergy μ ((Λ * ((2 : ℝ) ^ m)⁻¹) / ((2 : ℕ) ^ (n - m) : ℝ))
        (Λ * ((2 : ℝ) ^ m)⁻¹) ≤
      ENNReal.ofReal Λ * truncEnergy μ (dyadicRadius n) (dyadicRadius m) := by
  rw [enlarged_dyadic_grid_scale hmn]
  simpa only [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    using truncEnergy_enlarge_le μ (by positivity : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹)
      (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ m)⁻¹) hΛ

end FalconerPacking
