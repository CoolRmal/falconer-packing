/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialProjectionKernel
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative geometry of radial directions

Normalized radial vectors vary Lipschitz continuously away from the pin. The chordal
metric controls the difference of angles whenever the angles belong to a common chart.
-/

noncomputable section

open MeasureTheory Set

namespace FalconerPacking

/-- Normalization is quantitatively Lipschitz away from zero. -/
theorem norm_normalize_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v w : V} (hw : w ≠ 0) :
    ‖v‖ * ‖NormedSpace.normalize v - NormedSpace.normalize w‖ ≤ 2 * ‖v - w‖ := by
  have he : ‖v‖ • (NormedSpace.normalize v - NormedSpace.normalize w) =
      (v - w) + (‖w‖ - ‖v‖) • NormedSpace.normalize w := by
    rw [smul_sub, sub_smul, NormedSpace.norm_smul_normalize,
      NormedSpace.norm_smul_normalize]
    abel
  calc
    _ = ‖‖v‖ • (NormedSpace.normalize v - NormedSpace.normalize w)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
    _ = ‖(v - w) + (‖w‖ - ‖v‖) • NormedSpace.normalize w‖ := by rw [he]
    _ ≤ ‖v - w‖ + ‖(‖w‖ - ‖v‖) • NormedSpace.normalize w‖ := norm_add_le _ _
    _ = ‖v - w‖ + |‖w‖ - ‖v‖| := by
      rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hw, mul_one]
    _ ≤ 2 * ‖v - w‖ := by
      have h := abs_norm_sub_norm_le w v
      rw [norm_sub_rev w v] at h
      linarith

/-- Nearby source centers have nearby radial directions for a separated pin. -/
theorem norm_radialDirection_sub_le
    {b c y : EuclideanSpace ℝ (Fin 2)} {d : ℝ} (hd : 0 < d)
    (hb : d ≤ dist b y) (hc : d ≤ dist c y) :
    ‖angularDirection (radialAngle b y) - angularDirection (radialAngle c y)‖ ≤
      2 * dist b c / d := by
  have hby : b ≠ y := dist_pos.1 (hd.trans_le hb)
  have hcy : c ≠ y := dist_pos.1 (hd.trans_le hc)
  rw [angularDirection_radialAngle hby, angularDirection_radialAngle hcy]
  change ‖NormedSpace.normalize (b - y) - NormedSpace.normalize (c - y)‖ ≤ _
  rw [le_div_iff₀ hd]
  have h := norm_normalize_sub_le (sub_ne_zero.2 hcy) (v := b - y)
  rw [sub_sub_sub_cancel_right] at h
  have hb' : d ≤ ‖b - y‖ := by simpa only [dist_eq_norm] using hb
  have hmul := mul_le_mul_of_nonneg_right hb'
    (norm_nonneg (NormedSpace.normalize (b - y) - NormedSpace.normalize (c - y)))
  rw [dist_eq_norm]
  nlinarith

/-- Exact relation between chord length and the half-angle sine. -/
theorem norm_angularDirection_sub (θ φ : ℝ) :
    ‖angularDirection φ - angularDirection θ‖ = 2 * |Real.sin ((φ - θ) / 2)| := by
  rw [angularDirection, angularDirection, ← map_sub, LinearIsometryEquiv.norm_map,
    ← Complex.exp_ofReal_mul_I, ← Complex.exp_ofReal_mul_I]
  have he : Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((φ - θ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    congr 1
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- On an arc of length at most π, its parameter difference is controlled by its chord. -/
theorem abs_sub_le_pi_div_two_mul_chord {θ φ : ℝ} (h : |φ - θ| ≤ Real.pi) :
    |φ - θ| ≤ (Real.pi / 2) * ‖angularDirection φ - angularDirection θ‖ := by
  have hh : |(φ - θ) / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right h (by norm_num)
  have hs := Real.mul_abs_le_abs_sin hh
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  rw [norm_angularDirection_sub]
  have hpi := Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left hs hpi.le
  field_simp at hmul
  nlinarith

/-- A displacement bound supplies the circular closeness used in the Fourier comparison. -/
theorem radialAngle_chord_le_of_separation
    {b c y : EuclideanSpace ℝ (Fin 2)} {d r : ℝ} (hd : 0 < d)
    (hb : d ≤ dist b y) (hc : d ≤ dist c y) (hdisp : Real.pi * dist b c ≤ r * d) :
    (Real.pi / 2) *
      ‖angularDirection (radialAngle b y) - angularDirection (radialAngle c y)‖ ≤ r := by
  calc
    _ ≤ (Real.pi / 2) * (2 * dist b c / d) := mul_le_mul_of_nonneg_left
      (norm_radialDirection_sub_le hd hb hc) (by positivity)
    _ = Real.pi * dist b c / d := by ring
    _ ≤ r := (div_le_iff₀ hd).2 hdisp

end FalconerPacking
