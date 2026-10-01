/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicAngularCaps

/-!
# Actual anisotropic frequency rescaling of dyadic caps

The tangential scale is the square root of the annular radius and the radial scale is the radius.
The resulting Schwartz symbols have a common compact support independent of the annulus index.
-/

noncomputable section

open Set Metric SchwartzMap
open scoped ContDiff

namespace FalconerPacking

/-- The frequency map from unit cap coordinates to the actual dyadic annulus. -/
def capFrequencyRescaling (T n N j : ℕ) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (euclideanCoordinateDilation
    ![Real.sqrt ((2 : ℝ) ^ (T * n)), (2 : ℝ) ^ (T * n)] (by
      intro i
      fin_cases i <;> simp)).trans
    (circleCapFrame (angularGridPoint N j)).symm.toContinuousLinearEquiv

theorem capFrequencyRescaling_frame_zero (T n N j : ℕ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    circleCapFrame (angularGridPoint N j) (capFrequencyRescaling T n N j z) 0 =
      Real.sqrt ((2 : ℝ) ^ (T * n)) * z 0 := by
  simp [capFrequencyRescaling, euclideanCoordinateDilation_apply]

theorem capFrequencyRescaling_frame_one (T n N j : ℕ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    circleCapFrame (angularGridPoint N j) (capFrequencyRescaling T n N j z) 1 =
      (2 : ℝ) ^ (T * n) * z 1 := by
  simp [capFrequencyRescaling, euclideanCoordinateDilation_apply]

/-- The actual cap multiplier in normalized coordinates. -/
def rescaledDyadicAngularCap (T n N : ℕ) (hN : 0 < N) (j : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (capFrequencyRescaling T n N j)
    (dyadicAngularCap T n N hN j)

@[simp]
theorem rescaledDyadicAngularCap_apply (T n N : ℕ) (hN : 0 < N) (j : ℕ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    rescaledDyadicAngularCap T n N hN j z =
      dyadicAngularCap T n N hN j (capFrequencyRescaling T n N j z) := rfl

/-- The rescaled support has uniformly bounded transverse and radial coordinates. -/
theorem rescaledDyadicAngularCap_support_coordinates (T n N : ℕ) (hN : 0 < N)
    (hwidth : Real.sqrt ((2 : ℝ) ^ (T * n)) ≤ N) (j : ℕ)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Function.support
      (rescaledDyadicAngularCap T n N hN j)) :
    |z 0| ≤ 12 * Real.pi * 2 ^ T ∧ |z 1| ≤ 3 * (2 : ℝ) ^ T := by
  have h := dyadicAngularCap_rescaled_support T n N hN hwidth j
    (ξ := capFrequencyRescaling T n N j z) hz
  rw [capFrequencyRescaling_frame_zero, capFrequencyRescaling_frame_one,
    abs_mul, abs_mul, abs_of_pos (by positivity : 0 < Real.sqrt ((2 : ℝ) ^ (T * n))),
    abs_of_pos (by positivity : 0 < (2 : ℝ) ^ (T * n))] at h
  simpa only [mul_div_cancel_left₀ _ (by positivity : Real.sqrt ((2 : ℝ) ^ (T * n)) ≠ 0),
    mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ^ (T * n) ≠ 0)] using h

/-- One fixed closed ball contains the support of every rescaled cap in a block family. -/
theorem rescaledDyadicAngularCap_support_ball (T n N : ℕ) (hN : 0 < N)
    (hwidth : Real.sqrt ((2 : ℝ) ^ (T * n)) ≤ N) (j : ℕ) :
    Function.support (rescaledDyadicAngularCap T n N hN j) ⊆
      closedBall 0 ((12 * Real.pi + 3) * (2 : ℝ) ^ T) := by
  intro z hz
  obtain ⟨h₀, h₁⟩ := rescaledDyadicAngularCap_support_coordinates T n N hN hwidth j hz
  have hs := EuclideanSpace.real_norm_sq_eq z
  rw [Fin.sum_univ_two] at hs
  have hnorm : ‖z‖ ≤ |z 0| + |z 1| := by
    nlinarith [sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0), abs_nonneg (z 1),
      mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1)), norm_nonneg z]
  simp only [mem_closedBall, dist_zero_right]
  nlinarith

theorem circleCapFrame_direction_one (φ : ℝ) :
    circleCapFrame φ (angularDirection φ) 1 = 1 := by
  simp [circleCapFrame, planarRotation_angularDirection, angularDirection_apply_one]

/-- A unit directional ball keeps the radial coordinate at least half the radius. -/
theorem circleCapFrame_radial_ge_half_norm {ξ : EuclideanSpace ℝ (Fin 2)} {φ : ℝ}
    (hξ : ξ ≠ 0) (hd : ‖‖ξ‖⁻¹ • ξ - angularDirection φ‖ ≤ 1) :
    ‖ξ‖ / 2 ≤ circleCapFrame φ ξ 1 := by
  let u := circleCapFrame φ (‖ξ‖⁻¹ • ξ)
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hξ]
  have hv : circleCapFrame φ (angularDirection φ) = WithLp.toLp 2 ![0, 1] := by
    ext i
    fin_cases i
    · exact circleCapFrame_direction_zero φ
    · exact circleCapFrame_direction_one φ
  have hdu : ‖u - WithLp.toLp 2 ![0, 1]‖ ≤ 1 := by
    simpa only [u, ← hv, ← map_sub, LinearIsometryEquiv.norm_map] using hd
  have hs := EuclideanSpace.real_norm_sq_eq u
  rw [hu, Fin.sum_univ_two] at hs
  have ht := EuclideanSpace.real_norm_sq_eq (u - WithLp.toLp 2 ![0, 1])
  rw [Fin.sum_univ_two] at ht
  change _ = (u 0 - 0) ^ 2 + (u 1 - 1) ^ 2 at ht
  have hu₁ : (1 / 2 : ℝ) ≤ u 1 := by
    nlinarith [sq_nonneg (‖u - WithLp.toLp 2 ![0, 1]‖ - 1),
      norm_nonneg (u - WithLp.toLp 2 ![0, 1])]
  have hu₁' : (1 / 2 : ℝ) ≤ ‖ξ‖⁻¹ * circleCapFrame φ ξ 1 := by
    simpa [u, map_smul] using hu₁
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have h := mul_le_mul_of_nonneg_left hu₁' hnorm.le
  simpa [← mul_assoc, hnorm.ne', div_eq_mul_inv] using h

/-- At small angular width, the rescaled cap stays uniformly inside the positive radial chart. -/
theorem rescaledDyadicAngularCap_support_radial (T n N : ℕ) (hN : 0 < N)
    (hsmall : 4 * Real.pi ≤ N) (j : ℕ)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Function.support
      (rescaledDyadicAngularCap T n N hN j)) : 1 < z 1 := by
  let ξ := capFrequencyRescaling T n N j z
  have hR : 0 < (2 : ℝ) ^ (T * n) := by positivity
  have hs := dyadicAngularCap_radial_support T n N hN j (ξ := ξ) hz
  have hξ : ξ ≠ 0 := by intro he; simp only [he, norm_zero] at hs; linarith [hs.1]
  have hd := smoothAngularCap_direction_support _
    (hasCompactSupport_fourier_dyadicAnnularKernel T n)
    (fourier_dyadicAnnularKernel_eventually_zero T n) N hN j (ξ := ξ) hz
  have hwidth : 4 * Real.pi / (N : ℝ) ≤ 1 :=
    (div_le_one (by exact_mod_cast hN)).mpr hsmall
  have hdir₀ : ‖‖ξ‖⁻¹ • ξ - angularDirection (angularGridPoint N j)‖ ≤
      4 * Real.pi / N := by simpa only [dist_eq_norm] using (mem_ball.mp hd).le
  have hdir := hdir₀.trans hwidth
  have hr := circleCapFrame_radial_ge_half_norm hξ hdir
  rw [show ξ = capFrequencyRescaling T n N j z from rfl,
    capFrequencyRescaling_frame_one] at hr
  nlinarith [hs.1]

/-- The same non-strict radial bound holds on the topological support of the symbol. -/
theorem rescaledDyadicAngularCap_tsupport_radial (T n N : ℕ) (hN : 0 < N)
    (hsmall : 4 * Real.pi ≤ N) (j : ℕ) :
    tsupport (rescaledDyadicAngularCap T n N hN j) ⊆
      {z : EuclideanSpace ℝ (Fin 2) | 1 ≤ z 1} :=
  closure_minimal (fun _ hz ↦ (rescaledDyadicAngularCap_support_radial T n N hN hsmall j hz).le)
    (isClosed_le continuous_const (by fun_prop))

end FalconerPacking
