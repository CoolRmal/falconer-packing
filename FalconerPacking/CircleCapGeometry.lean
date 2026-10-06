/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircularPlancherel
public import FalconerPacking.RadialProjectionTransversality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Rectangular localization of circular frequency arcs

An arc has tangential displacement linear in its angular width and normal displacement
quadratic in that width. The estimates include a bounded frequency thickening and turn
the admissibility inequality between spatial scales into the required Fourier rectangle.
-/

@[expose] public section

noncomputable section

open Set Metric
open scoped RealInnerProductSpace

namespace FalconerPacking

theorem angularDirection_apply_zero (θ : ℝ) : angularDirection θ 0 = Real.cos θ := by
  simp only [angularDirection, Complex.orthonormalBasisOneI_repr_apply,
    Matrix.cons_val_zero, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero]

theorem angularDirection_apply_one (θ : ℝ) : angularDirection θ 1 = Real.sin θ := by
  simp only [angularDirection, Complex.orthonormalBasisOneI_repr_apply,
    Matrix.cons_val_one, Matrix.cons_val_zero, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, zero_mul, add_zero, zero_add]

/-- The transverse coordinate comes first, as in the dual rectangles used for embedding. -/
def circleCapFrame (φ : ℝ) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  planarRotation (Real.pi / 2 - φ)

theorem circleCapFrame_arc_zero (r θ φ : ℝ) :
    circleCapFrame φ (r • angularDirection θ - r • angularDirection φ) 0 =
      -r * Real.sin (θ - φ) := by
  simp only [circleCapFrame, map_sub, map_smul, planarRotation_angularDirection,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, angularDirection_apply_zero]
  rw [show Real.pi / 2 - φ + θ = (θ - φ) + Real.pi / 2 by ring,
    show Real.pi / 2 - φ + φ = Real.pi / 2 by ring,
    Real.cos_add_pi_div_two, Real.cos_pi_div_two]
  ring

theorem circleCapFrame_arc_one (r θ φ : ℝ) :
    circleCapFrame φ (r • angularDirection θ - r • angularDirection φ) 1 =
      r * (Real.cos (θ - φ) - 1) := by
  simp only [circleCapFrame, map_sub, map_smul, planarRotation_angularDirection,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, angularDirection_apply_one]
  rw [show Real.pi / 2 - φ + θ = (θ - φ) + Real.pi / 2 by ring,
    show Real.pi / 2 - φ + φ = Real.pi / 2 by ring,
    Real.sin_add_pi_div_two, Real.sin_pi_div_two]
  ring

/-- The normal displacement from the tangent line is at most half the squared angle. -/
theorem abs_cos_sub_one_le_sq_half (x : ℝ) : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one x))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- Actual circular arcs lie in the expected tangential-by-normal rectangle. -/
theorem circleCapFrame_arc_bounds {r δ θ φ : ℝ}
    (hr : 0 ≤ r) (hθ : |θ - φ| ≤ δ) :
    |circleCapFrame φ (r • angularDirection θ - r • angularDirection φ) 0| ≤ r * δ ∧
    |circleCapFrame φ (r • angularDirection θ - r • angularDirection φ) 1| ≤
      r * δ ^ 2 / 2 := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hθ
  constructor
  · rw [circleCapFrame_arc_zero, abs_mul, abs_neg, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs.trans hθ) hr
  · rw [circleCapFrame_arc_one, abs_mul, abs_of_nonneg hr]
    have hs : (θ - φ) ^ 2 ≤ δ ^ 2 := by
      nlinarith [sq_abs (θ - φ), sq_le_sq₀ (abs_nonneg (θ - φ)) hδ |>.mpr hθ]
    have hc := (abs_cos_sub_one_le_sq_half (θ - φ)).trans
      (div_le_div_of_nonneg_right hs (by norm_num))
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hc hr

/-- Thickening a circular arc adds at most the thickening radius in either coordinate. -/
theorem circleCapFrame_thickened_bounds {r δ θ φ ε : ℝ}
    (hr : 0 ≤ r) (hθ : |θ - φ| ≤ δ)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ ≤ ε) :
    |circleCapFrame φ (r • angularDirection θ + z - r • angularDirection φ) 0| ≤
      r * δ + ε ∧
    |circleCapFrame φ (r • angularDirection θ + z - r • angularDirection φ) 1| ≤
      r * δ ^ 2 / 2 + ε := by
  obtain ⟨h₀, h₁⟩ := circleCapFrame_arc_bounds hr hθ
  have he (i : Fin 2) : |circleCapFrame φ z i| ≤ ε := by
    simpa only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] using
      (PiLp.norm_apply_le (circleCapFrame φ z) i).trans
        (by simpa only [LinearIsometryEquiv.norm_map] using hz)
  have hdecomp : r • angularDirection θ + z - r • angularDirection φ =
      (r • angularDirection θ - r • angularDirection φ) + z := by abel
  rw [hdecomp, map_add]
  constructor
  · exact (abs_add_le _ _).trans (add_le_add h₀ (he 0))
  · exact (abs_add_le _ _).trans (add_le_add h₁ (he 1))

/-- Admissible spatial scales control both curvature and the fixed smoothing radius. -/
theorem circleCapFrame_admissible_rectangle {R C r a b θ φ : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hr : 0 ≤ r) (hrR : r ≤ C * R)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hab : b ≤ R * a ^ 2) (hθ : |θ - φ| ≤ (R * a)⁻¹)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ ≤ 1) :
    |circleCapFrame φ (r • angularDirection θ + z - r • angularDirection φ) 0| ≤
      (C + 1) / a ∧
    |circleCapFrame φ (r • angularDirection θ + z - r • angularDirection φ) 1| ≤
      (C + 1) / b := by
  obtain ⟨h₀, h₁⟩ := circleCapFrame_thickened_bounds hr hθ z hz
  have ht : r * (R * a)⁻¹ ≤ C / a := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ (mul_pos hR ha) ha]
    nlinarith
  have hn : r * ((R * a)⁻¹) ^ 2 / 2 ≤ C / b := by
    have hd : r * ((R * a)⁻¹) ^ 2 / 2 = r / (2 * R ^ 2 * a ^ 2) := by
      field_simp
    rw [hd, div_le_div_iff₀ (by positivity) hb]
    have hprod := mul_le_mul hrR hab hb.le (mul_nonneg hC hR.le)
    nlinarith [mul_nonneg hC (mul_nonneg (sq_nonneg R) (sq_nonneg a))]
  constructor
  · apply h₀.trans
    have : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha₁)
    calc
      _ ≤ C / a + 1 / a := add_le_add ht this
      _ = (C + 1) / a := by ring
  · apply h₁.trans
    have : 1 ≤ 1 / b := (le_div_iff₀ hb).mpr (by simpa using hb₁)
    calc
      _ ≤ C / b + 1 / b := add_le_add hn this
      _ = (C + 1) / b := by ring

end FalconerPacking
