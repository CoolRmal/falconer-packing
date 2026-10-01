/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleCapScaledGeometry

/-!
# Curvature rectangles from chord distance

Grouped smooth standard caps can cross the angular branch cut. Unit-vector chord
geometry gives the same quadratic normal displacement without choosing an angular lift.
-/

noncomputable section

open Set Metric
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- Unit vectors have exactly quadratic displacement normal to the tangent line. -/
theorem circleCapFrame_normal_chord (φ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ = 1) :
    circleCapFrame φ (v - angularDirection φ) 1 =
      -(dist v (angularDirection φ)) ^ 2 / 2 := by
  rw [circleCapFrame_one_eq_inner, inner_sub_right,
    real_inner_self_eq_norm_sq, norm_angularDirection]
  have h := norm_sub_sq_real v (angularDirection φ)
  rw [hv, norm_angularDirection, real_inner_comm (angularDirection φ) v] at h
  rw [dist_eq_norm]
  nlinarith

/-- The transverse/normal displacement estimates hold directly for chord widths. -/
theorem circleCapFrame_chord_bounds {r δ φ : ℝ} (hr : 0 ≤ r)
    (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ = 1)
    (hd : dist v (angularDirection φ) ≤ δ) :
    |circleCapFrame φ (r • v - r • angularDirection φ) 0| ≤ r * δ ∧
      |circleCapFrame φ (r • v - r • angularDirection φ) 1| ≤ r * δ ^ 2 / 2 := by
  have hδ : 0 ≤ δ := dist_nonneg.trans hd
  rw [← smul_sub, map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hr]
  constructor
  · have hc : |circleCapFrame φ (v - angularDirection φ) 0| ≤
        dist v (angularDirection φ) := by
      simpa only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map, dist_eq_norm] using
        PiLp.norm_apply_le (circleCapFrame φ (v - angularDirection φ)) 0
    exact mul_le_mul_of_nonneg_left (hc.trans hd) hr
  · rw [circleCapFrame_normal_chord φ v hv, abs_div, abs_neg, abs_pow,
      abs_of_nonneg dist_nonneg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hs := (sq_le_sq₀ dist_nonneg hδ).mpr hd
    nlinarith [mul_le_mul_of_nonneg_left hs hr]

/-- Fixed spectral smoothing preserves the chord-based curvature estimate. -/
theorem circleCapFrame_thickened_chord_bounds {r δ φ ε : ℝ} (hr : 0 ≤ r)
    (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ = 1)
    (hd : dist v (angularDirection φ) ≤ δ)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ ≤ ε) :
    |circleCapFrame φ (r • v + z - r • angularDirection φ) 0| ≤ r * δ + ε ∧
      |circleCapFrame φ (r • v + z - r • angularDirection φ) 1| ≤ r * δ ^ 2 / 2 + ε := by
  obtain ⟨h₀, h₁⟩ := circleCapFrame_chord_bounds hr v hv hd
  have he (i : Fin 2) : |circleCapFrame φ z i| ≤ ε := by
    simpa only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] using
      (PiLp.norm_apply_le (circleCapFrame φ z) i).trans
        (by simpa only [LinearIsometryEquiv.norm_map] using hz)
  rw [show r • v + z - r • angularDirection φ =
    (r • v - r • angularDirection φ) + z by abel, map_add]
  exact ⟨(abs_add_le _ _).trans (add_le_add h₀ (he 0)),
    (abs_add_le _ _).trans (add_le_add h₁ (he 1))⟩

/-- A fixed chord multiple gives an admissible thickened rectangle with an absolute constant. -/
theorem circleCapFrame_chord_admissible_rectangle {R r a b φ : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ 2 * R)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hab : b ≤ R * a ^ 2) (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ = 1)
    (hd : dist v (angularDirection φ) ≤ 24 / (R * a))
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ ≤ 1) :
    |circleCapFrame φ (r • v + z - r • angularDirection φ) 0| ≤ 1000 / a ∧
      |circleCapFrame φ (r • v + z - r • angularDirection φ) 1| ≤ 1000 / b := by
  obtain ⟨h₀, h₁⟩ := circleCapFrame_thickened_chord_bounds hr v hv hd z hz
  have ht : r * (24 / (R * a)) ≤ 48 / a := by
    rw [show r * (24 / (R * a)) = 24 * (r / (R * a)) by ring]
    have : r / (R * a) ≤ 2 / a := by
      rw [div_le_div_iff₀ (mul_pos hR ha) ha]
      nlinarith
    calc
      _ ≤ 24 * (2 / a) := by gcongr
      _ = _ := by ring
  have hn : r * (24 / (R * a)) ^ 2 / 2 ≤ 576 / b := by
    have hd' : r * (24 / (R * a)) ^ 2 / 2 =
        576 * (r / (2 * R ^ 2 * a ^ 2)) := by field_simp; ring
    rw [hd']
    have : r / (2 * R ^ 2 * a ^ 2) ≤ 1 / b := by
      rw [div_le_div_iff₀ (by positivity) hb]
      have hprod := mul_le_mul hrR hab hb.le (by positivity : 0 ≤ 2 * R)
      nlinarith
    calc
      _ ≤ 576 * (1 / b) := by gcongr
      _ = _ := by ring
  have haunit : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha₁)
  have hbunit : 1 ≤ 1 / b := (le_div_iff₀ hb).mpr (by simpa using hb₁)
  constructor
  · apply h₀.trans
    calc
      _ ≤ 48 / a + 1 / a := add_le_add ht haunit
      _ = 49 / a := by ring
      _ ≤ _ := by gcongr; norm_num
  · apply h₁.trans
    calc
      _ ≤ 576 / b + 1 / b := add_le_add hn hbunit
      _ = 577 / b := by ring
      _ ≤ _ := by gcongr; norm_num

end FalconerPacking
