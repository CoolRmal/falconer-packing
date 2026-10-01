/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SmoothAngularCaps
import FalconerPacking.DyadicAnnularKernel
import FalconerPacking.CircleCapGeometry

/-!+# Actual smooth angular caps of a dyadic annulus

The previously constructed angular partition is applied to the actual dyadic multiplier.
Its support, after tangential square-root scaling and radial scaling, lies in a fixed rectangle.
-/

noncomputable section

open Set Metric Filter SchwartzMap FourierTransform
open scoped ContDiff Topology

namespace FalconerPacking

theorem hasCompactSupport_fourier_dyadicAnnularKernel (T n : ℕ) :
    HasCompactSupport (𝓕 (dyadicAnnularKernel T n) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall 0 (3 * (2 : ℝ) ^ (T * (n + 1))))
  intro ξ hξ
  simp only [mem_closedBall, dist_zero_right]
  exact le_of_not_ge fun he ↦ hξ (fourier_dyadicAnnularKernel_eq_zero T n (Or.inr he))

theorem fourier_dyadicAnnularKernel_eventually_zero (T n : ℕ) :
    (𝓕 (dyadicAnnularKernel T n) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) =ᶠ[𝓝 0]
      (0 : EuclideanSpace ℝ (Fin 2) → ℂ) := by
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 2))
    (by positivity : 0 < 2 * (2 : ℝ) ^ (T * n))] with ξ hξ
  exact fourier_dyadicAnnularKernel_eq_zero T n
    (Or.inl (by simpa only [dist_zero_right] using (mem_ball.mp hξ).le))

/-- A cap of the actual dyadic annular multiplier. -/
def dyadicAngularCap (T n N : ℕ) (hN : 0 < N) (j : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  smoothAngularCap (𝓕 (dyadicAnnularKernel T n))
    (hasCompactSupport_fourier_dyadicAnnularKernel T n)
    (fourier_dyadicAnnularKernel_eventually_zero T n) N hN j

/-- These are a genuine finite partition of the annular multiplier. -/
theorem sum_dyadicAngularCap (T n N : ℕ) (hN : 0 < N) :
    ∑ j ∈ Finset.range N, dyadicAngularCap T n N hN j =
      𝓕 (dyadicAnnularKernel T n) :=
  sum_smoothAngularCap _ _ _ N hN

/-- Both radial support bounds follow from the constructed low-pass differences. -/
theorem dyadicAngularCap_radial_support (T n N : ℕ) (hN : 0 < N) (j : ℕ)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ∈ Function.support (dyadicAngularCap T n N hN j)) :
    2 * (2 : ℝ) ^ (T * n) < ‖ξ‖ ∧ ‖ξ‖ < 3 * 2 ^ T * 2 ^ (T * n) := by
  have hs := support_smoothAngularCap_subset _ _ _ N hN j hξ
  constructor
  · exact lt_of_not_ge fun he ↦ hs (fourier_dyadicAnnularKernel_eq_zero T n (Or.inl he))
  · have he : ¬3 * (2 : ℝ) ^ (T * (n + 1)) ≤ ‖ξ‖ :=
      fun he ↦ hs (fourier_dyadicAnnularKernel_eq_zero T n (Or.inr he))
    simpa [Nat.mul_add, pow_add, mul_assoc, mul_comm, mul_left_comm] using lt_of_not_ge he

theorem circleCapFrame_direction_zero (φ : ℝ) :
    circleCapFrame φ (angularDirection φ) 0 = 0 := by
  simp [circleCapFrame, planarRotation_angularDirection, angularDirection_apply_zero]

/-- A directional ball gives a transverse coordinate bound without choosing an angle chart. -/
theorem circleCapFrame_transverse_le {ξ : EuclideanSpace ℝ (Fin 2)} {φ δ : ℝ}
    (hξ : ξ ≠ 0) (hd : ‖‖ξ‖⁻¹ • ξ - angularDirection φ‖ ≤ δ) :
    |circleCapFrame φ ξ 0| ≤ ‖ξ‖ * δ := by
  have he : ξ - ‖ξ‖ • angularDirection φ =
      ‖ξ‖ • (‖ξ‖⁻¹ • ξ - angularDirection φ) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ), one_smul]
  have hc : circleCapFrame φ (ξ - ‖ξ‖ • angularDirection φ) 0 =
      circleCapFrame φ ξ 0 := by
    simp [map_sub, map_smul, circleCapFrame_direction_zero]
  calc
    _ = |circleCapFrame φ (ξ - ‖ξ‖ • angularDirection φ) 0| := congrArg abs hc.symm
    _ ≤ ‖ξ - ‖ξ‖ • angularDirection φ‖ := by
      simpa only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] using
        PiLp.norm_apply_le (circleCapFrame φ (ξ - ‖ξ‖ • angularDirection φ)) 0
    _ = ‖ξ‖ * ‖‖ξ‖⁻¹ • ξ - angularDirection φ‖ := by simp [he, norm_smul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (norm_nonneg ξ)

/-- Tangential and radial rescaling give a rectangle independent of the annulus index. -/
theorem dyadicAngularCap_rescaled_support (T n N : ℕ) (hN : 0 < N)
    (hwidth : Real.sqrt ((2 : ℝ) ^ (T * n)) ≤ N) (j : ℕ)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ∈ Function.support (dyadicAngularCap T n N hN j)) :
    |circleCapFrame (angularGridPoint N j) ξ 0| / Real.sqrt (2 ^ (T * n)) ≤
        12 * Real.pi * 2 ^ T ∧
      |circleCapFrame (angularGridPoint N j) ξ 1| / (2 : ℝ) ^ (T * n) ≤ 3 * 2 ^ T := by
  have hR : 0 < (2 : ℝ) ^ (T * n) := by positivity
  have hs := dyadicAngularCap_radial_support T n N hN j hξ
  have hnξ : ξ ≠ 0 := by intro he; simp only [he, norm_zero] at hs; linarith [hs.1]
  have hd := smoothAngularCap_direction_support _ _ _ N hN j hξ
  have ht := circleCapFrame_transverse_le hnξ
    (by simpa only [dist_eq_norm] using (mem_ball.mp hd).le)
  constructor
  · rw [div_le_iff₀ (Real.sqrt_pos.mpr hR)]
    have hδ : 4 * Real.pi / (N : ℝ) ≤
        4 * Real.pi / Real.sqrt ((2 : ℝ) ^ (T * n)) :=
      div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hR) hwidth
    calc
      _ ≤ ‖ξ‖ * (4 * Real.pi / Real.sqrt ((2 : ℝ) ^ (T * n))) :=
        ht.trans (mul_le_mul_of_nonneg_left hδ (norm_nonneg ξ))
      _ ≤ (3 * 2 ^ T * (2 : ℝ) ^ (T * n)) *
          (4 * Real.pi / Real.sqrt ((2 : ℝ) ^ (T * n))) := by gcongr; exact hs.2.le
      _ = _ := by
        have he := Real.sq_sqrt hR.le
        field_simp
        nlinarith
  · rw [div_le_iff₀ hR]
    have hc : |circleCapFrame (angularGridPoint N j) ξ 1| ≤ ‖ξ‖ := by
      simpa only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] using
        PiLp.norm_apply_le (circleCapFrame (angularGridPoint N j) ξ) 1
    exact hc.trans hs.2.le

end FalconerPacking
