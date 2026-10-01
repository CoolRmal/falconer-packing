/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PhysicalDyadicCapKernels
import FalconerPacking.SchwartzRadialTails

/-!
# Actual spatial tails of physical cap kernels

Every coordinate expands by at least the square root of the frequency. Radial Schwartz
tails therefore control the physical kernel outside a fixed source neighborhood.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The physical dilation expands every vector by at least the square-root frequency. -/
theorem sqrt_frequency_mul_norm_le_capSpatialRescaling (T n N j : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Real.sqrt ((2 : ℝ) ^ (T * n)) * ‖x‖ ≤ ‖capSpatialRescaling T n N j x‖ := by
  let R := (2 : ℝ) ^ (T * n)
  let O := circleCapFrame (angularGridPoint N j)
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR₀ : 0 ≤ R := by positivity
  have h₀ : capSpatialRescaling T n N j x 0 = Real.sqrt R * O x 0 := by
    simp only [capSpatialRescaling, orientedRectangleDilation_apply_zero, div_inv_eq_mul]
    ring
  have h₁ : capSpatialRescaling T n N j x 1 = R * O x 1 := by
    simp only [capSpatialRescaling, orientedRectangleDilation_apply_one, div_inv_eq_mul]
    ring
  have hs := EuclideanSpace.real_norm_sq_eq (capSpatialRescaling T n N j x)
  rw [Fin.sum_univ_two, h₀, h₁, mul_pow, mul_pow, Real.sq_sqrt hR₀] at hs
  have ht := EuclideanSpace.real_norm_sq_eq (O x)
  rw [Fin.sum_univ_two, LinearIsometryEquiv.norm_map] at ht
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  change (Real.sqrt R * ‖x‖) ^ 2 ≤ _
  rw [mul_pow, Real.sq_sqrt hR₀]
  nlinarith [mul_nonneg (show 0 ≤ R ^ 2 - R by nlinarith) (sq_nonneg (O x 1))]

/-- Physical radial tails are bounded by normalized radial tails at the expanded radius. -/
theorem lintegral_radial_tail_fourierInv_dyadicAngularCap_le
    (T n N : ℕ) (hN : 0 < N) (j : ℕ) (w : ℝ) :
    (∫⁻ x in {x | w ≤ ‖x‖}, ‖(𝓕⁻ (dyadicAngularCap T n N hN j) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) ≤
    ∫⁻ z in {z | Real.sqrt ((2 : ℝ) ^ (T * n)) * w ≤ ‖z‖},
      ‖(𝓕⁻ (rescaledDyadicAngularCap T n N hN j) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) z‖ₑ := by
  let S := {z : EuclideanSpace ℝ (Fin 2) |
    Real.sqrt ((2 : ℝ) ^ (T * n)) * w ≤ ‖z‖}
  have hS : MeasurableSet S := isClosed_le continuous_const continuous_norm |>.measurableSet
  have hsub : {x : EuclideanSpace ℝ (Fin 2) | w ≤ ‖x‖} ⊆
      (capSpatialRescaling T n N j) ⁻¹' S := by
    intro x hx
    exact (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)).trans
      (sqrt_frequency_mul_norm_le_capSpatialRescaling T n N j x)
  rw [fourierInv_dyadicAngularCap_eq_rescaled]
  exact (lintegral_mono_set hsub).trans_eq (setLIntegral_enorm_rescaledSchwartzKernel _ _ hS)

/-- The actual physical cap family has all radial tail powers uniformly in scale. -/
theorem dyadicCapKernel_uniform_radial_tail {ι : Type*} (T : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (n N j : ι → ℕ) (hN : ∀ i, 0 < N i)
    (hwidth : ∀ i, Real.sqrt ((2 : ℝ) ^ (T * n i)) ≤ N i)
    (hsmall : ∀ i, 4 * Real.pi ≤ N i)
    (hupper : ∀ i, (N i : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n i)))
    (m : ℕ) :
    ∃ C > 0, ∀ i (w : ℝ), 0 < w →
      (∫⁻ x in {x | w ≤ ‖x‖},
        ‖(𝓕⁻ (dyadicAngularCap T (n i) (N i) (hN i) (j i)) :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) ≤
        ENNReal.ofReal (C / (Real.sqrt ((2 : ℝ) ^ (T * n i)) * w) ^ m) := by
  have hb := isVonNBounded_rescaledDyadicCapKernel_range T hK n N j hN hwidth hsmall hupper
  obtain ⟨C, hC, hc⟩ := exists_uniform_schwartz_radial_tail _ hb m
  exact ⟨C, hC, fun i w hw ↦
    (lintegral_radial_tail_fourierInv_dyadicAngularCap_le T (n i) (N i) (hN i) (j i) w).trans
      (hc i _ (by positivity))⟩

end FalconerPacking
