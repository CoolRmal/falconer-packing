/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleCapGeometry
import FalconerPacking.CapLabelGeometry
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Fixed-width cap rectangles and inherited physical frames

The actual angular grid has width `2π / F`. This file retains that fixed factor in
admissible rectangles and compares its Fourier frame with the inherited standard frame.
-/

noncomputable section

open Set Metric
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- The grid's fixed angular factor changes only the constant in the dual rectangle. -/
theorem circleCapFrame_scaled_admissible_rectangle {R D r a b θ φ : ℝ}
    (hR : 0 < R) (hD : 0 ≤ D) (hr : 0 ≤ r) (hrR : r ≤ 2 * R)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hab : b ≤ R * a ^ 2) (hθ : |θ - φ| ≤ D / (R * a))
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ ≤ 1) :
    |circleCapFrame φ (r • angularDirection θ + z - r • angularDirection φ) 0| ≤
      (2 * D + 1) / a ∧
    |circleCapFrame φ (r • angularDirection θ + z - r • angularDirection φ) 1| ≤
      (D ^ 2 + 1) / b := by
  obtain ⟨h₀, h₁⟩ := circleCapFrame_thickened_bounds hr hθ z hz
  have ht : r * (D / (R * a)) ≤ 2 * D / a := by
    have : r / (R * a) ≤ 2 / a := by
      rw [div_le_div_iff₀ (mul_pos hR ha) ha]
      nlinarith
    calc
      _ = D * (r / (R * a)) := by ring
      _ ≤ D * (2 / a) := mul_le_mul_of_nonneg_left this hD
      _ = _ := by ring
  have hn : r * (D / (R * a)) ^ 2 / 2 ≤ D ^ 2 / b := by
    have hd : r * (D / (R * a)) ^ 2 / 2 = D ^ 2 * (r / (2 * R ^ 2 * a ^ 2)) := by
      field_simp
    rw [hd]
    have : r / (2 * R ^ 2 * a ^ 2) ≤ 1 / b := by
      rw [div_le_div_iff₀ (by positivity) hb]
      have hprod := mul_le_mul hrR hab hb.le (by positivity : 0 ≤ 2 * R)
      nlinarith
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left this (sq_nonneg D)
  constructor
  · have hunit : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha₁)
    exact h₀.trans (by calc
      _ ≤ 2 * D / a + 1 / a := add_le_add ht hunit
      _ = _ := by ring)
  · have hunit : 1 ≤ 1 / b := (le_div_iff₀ hb).mpr (by simpa using hb₁)
    exact h₁.trans (by calc
      _ ≤ D ^ 2 / b + 1 / b := add_le_add hn hunit
      _ = _ := by ring)

/-- The normal coordinate is the scalar product with the cap's central direction. -/
theorem circleCapFrame_one_eq_inner (φ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    circleCapFrame φ x 1 = ⟪angularDirection φ, x⟫ := by
  simp only [circleCapFrame, planarRotation_apply, Complex.orthonormalBasisOneI_repr_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.add_im,
    Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, sub_zero,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, PiLp.inner_apply, Fin.sum_univ_two,
    Real.inner_apply, angularDirection_apply_zero, angularDirection_apply_one]
  ring

/-- The transverse coordinate is the scalar product with the clockwise unit normal. -/
theorem circleCapFrame_zero_eq_inner (φ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    circleCapFrame φ x 0 = ⟪angularDirection (φ - Real.pi / 2), x⟫ := by
  simp only [circleCapFrame, planarRotation_apply, Complex.orthonormalBasisOneI_repr_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Matrix.cons_val_zero, Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, sub_zero,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, PiLp.inner_apply, Fin.sum_univ_two,
    Real.inner_apply, angularDirection_apply_zero, angularDirection_apply_one,
    Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
  ring

/-- The difference of cap frames is bounded by the chord distance, including across the branch cut. -/
theorem circleCapFrame_sub_le (θ φ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |circleCapFrame θ x i - circleCapFrame φ x i| ≤
      dist (angularDirection θ) (angularDirection φ) * ‖x‖ := by
  have h (v w : EuclideanSpace ℝ (Fin 2)) :
      |⟪v, x⟫ - ⟪w, x⟫| ≤ dist v w * ‖x‖ := by
    rw [← inner_sub_left, dist_eq_norm]
    exact abs_real_inner_le_norm _ _
  fin_cases i
  · change |circleCapFrame θ x 0 - circleCapFrame φ x 0| ≤ _
    rw [circleCapFrame_zero_eq_inner, circleCapFrame_zero_eq_inner]
    have hd : dist (angularDirection (θ - Real.pi / 2))
        (angularDirection (φ - Real.pi / 2)) =
        dist (angularDirection θ) (angularDirection φ) := by
      have := (planarRotation (-Real.pi / 2)).dist_map
        (angularDirection θ) (angularDirection φ)
      simpa only [planarRotation_angularDirection,
        show -Real.pi / 2 + θ = θ - Real.pi / 2 by ring,
        show -Real.pi / 2 + φ = φ - Real.pi / 2 by ring] using this
    simpa only [hd] using h (angularDirection (θ - Real.pi / 2))
      (angularDirection (φ - Real.pi / 2))
  · change |circleCapFrame θ x 1 - circleCapFrame φ x 1| ≤ _
    rw [circleCapFrame_one_eq_inner, circleCapFrame_one_eq_inner]
    exact h _ _

/-- All fine descendants of one standard cap use its common physical frame. -/
theorem fineCapLabels_frame_perturbation {S F : ℕ} (hS : 0 < S) (hSF : S ≤ F)
    {a b : ℝ} (hscale : (S : ℝ)⁻¹ ≤ a / b) {p : ℕ × ℕ}
    (hp : p ∈ fineCapLabels S F) (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |circleCapFrame (angularGridPoint S p.1) x i -
      circleCapFrame (angularGridPoint F p.2) x i| ≤ 24 * (a / b) * ‖x‖ := by
  have hc : dist (angularDirection (angularGridPoint S p.1))
      (angularDirection (angularGridPoint F p.2)) ≤ 24 * (a / b) := by
    calc
      _ ≤ 6 * Real.pi / S := (fineCapLabels_centers_close hS hSF hp).le
      _ ≤ 24 / S := by gcongr; linarith [Real.pi_lt_four]
      _ = 24 * (S : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 24 * (a / b) := mul_le_mul_of_nonneg_left hscale (by norm_num)
  exact (circleCapFrame_sub_le _ _ x i).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg x))

end FalconerPacking
