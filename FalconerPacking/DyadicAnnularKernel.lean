/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.OrientedReproducingKernel

/-!
# Actual smooth dyadic annular kernels

The low-pass multiplier is the fixed smooth cutoff evaluated at the reciprocal frequency scale.
Its inverse transform is a rescaled Schwartz kernel. Consecutive differences have annular
Fourier support, a uniform first-norm bound, and an exact finite telescoping identity.
-/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal RealInnerProductSpace Topology

namespace FalconerPacking

/-- The smooth low-pass kernel at positive frequency scale `a`. -/
def lowpassSchwartzKernel (a : ℝ) (ha : 0 < a) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  anisotropicReproducingKernel (euclideanCoordinateDilation (fun _ ↦ a) (fun _ ↦ ha.ne'))

theorem lowpassSchwartzKernel_apply (a : ℝ) (ha : 0 < a)
    (x : EuclideanSpace ℝ (Fin 2)) :
    lowpassSchwartzKernel a ha x = a ^ 2 • unitReproducingKernel (a • x) := by
  rw [lowpassSchwartzKernel, anisotropicReproducingKernel_apply,
    euclideanCoordinateDilation_det]
  have hA : euclideanCoordinateDilation (fun _ : Fin 2 ↦ a) (fun _ ↦ ha.ne') x = a • x := by
    ext i
    rfl
  rw [hA, abs_of_pos (mul_pos ha ha), pow_two]

/-- The low-pass multiplier is the explicitly rescaled compact smooth cutoff. -/
theorem fourier_lowpassSchwartzKernel (a : ℝ) (ha : 0 < a)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    (𝓕 (lowpassSchwartzKernel a ha) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ =
      unitFrequencyCutoff (a⁻¹ • ξ) := by
  rw [lowpassSchwartzKernel, fourier_anisotropicReproducingKernel]
  congr 1
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hA : (euclideanCoordinateDilation (fun _ : Fin 2 ↦ a)
      (fun _ ↦ ha.ne')).symm x = a⁻¹ • x := by
    ext i
    rfl
  rw [ContinuousLinearEquiv.coe_coe, hA]
  simp [real_inner_smul_left, real_inner_smul_right]

/-- The multiplier is exactly one on the radius `2a` ball. -/
theorem fourier_lowpassSchwartzKernel_eq_one (a : ℝ) (ha : 0 < a)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ‖ξ‖ ≤ 2 * a) :
    (𝓕 (lowpassSchwartzKernel a ha) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ = 1 := by
  rw [fourier_lowpassSchwartzKernel]
  change (unitFrequencyBump (a⁻¹ • ξ) : ℂ) = 1
  rw [unitFrequencyBump.one_of_mem_closedBall]
  · norm_num
  · simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos ha, unitFrequencyBump]
    exact (inv_mul_le_iff₀ ha).mpr (by simpa [mul_comm] using hξ)

/-- The multiplier vanishes outside the radius `3a` ball. -/
theorem fourier_lowpassSchwartzKernel_eq_zero (a : ℝ) (ha : 0 < a)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : 3 * a ≤ ‖ξ‖) :
    (𝓕 (lowpassSchwartzKernel a ha) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ = 0 := by
  rw [fourier_lowpassSchwartzKernel]
  apply unitFrequencyCutoff_eq_zero
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
  exact (le_inv_mul_iff₀ ha).mpr (by simpa [mul_comm] using hξ)

/-- The low-pass kernel has total integral one, despite not requiring pointwise positivity. -/
theorem integral_lowpassSchwartzKernel (a : ℝ) (ha : 0 < a) :
    (∫ x, lowpassSchwartzKernel a ha x) = 1 := by
  have h := fourier_lowpassSchwartzKernel_eq_one a ha
    (ξ := 0) (by simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) ha).le)
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq] using h

/-- The first norm is independent of frequency scale. -/
theorem integral_norm_lowpassSchwartzKernel (a : ℝ) (ha : 0 < a) :
    (∫ x, ‖lowpassSchwartzKernel a ha x‖) = ∫ x, ‖unitReproducingKernel x‖ := by
  rw [integral_norm_eq_lintegral_enorm (lowpassSchwartzKernel a ha).integrable.aestronglyMeasurable,
    integral_norm_eq_lintegral_enorm unitReproducingKernel.integrable.aestronglyMeasurable]
  congr 1
  exact anisotropicReproducingKernel_lintegral_enorm _

/-- A full smooth annular kernel, before any angular or spatial packet decomposition. -/
def dyadicAnnularKernel (T n : ℕ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  lowpassSchwartzKernel (2 ^ (T * (n + 1))) (by positivity) -
    lowpassSchwartzKernel (2 ^ (T * n)) (by positivity)

/-- The annular multiplier is the difference of the two actual smooth low-pass multipliers. -/
theorem fourier_dyadicAnnularKernel (T n : ℕ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    (𝓕 (dyadicAnnularKernel T n) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ =
      unitFrequencyCutoff ((2 ^ (T * (n + 1)) : ℝ)⁻¹ • ξ) -
        unitFrequencyCutoff ((2 ^ (T * n) : ℝ)⁻¹ • ξ) := by
  change (SchwartzMap.fourierTransformCLM ℂ
    (lowpassSchwartzKernel _ _ - lowpassSchwartzKernel _ _)) ξ = _
  rw [map_sub]
  simp only [sub_apply, SchwartzMap.fourierTransformCLM_apply,
    fourier_lowpassSchwartzKernel]

/-- The multiplier vanishes both below its inner scale and beyond its outer scale. -/
theorem fourier_dyadicAnnularKernel_eq_zero (T n : ℕ)
    {ξ : EuclideanSpace ℝ (Fin 2)}
    (hξ : ‖ξ‖ ≤ 2 * 2 ^ (T * n) ∨ 3 * 2 ^ (T * (n + 1)) ≤ ‖ξ‖) :
    (𝓕 (dyadicAnnularKernel T n) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ = 0 := by
  have hscale : (2 : ℝ) ^ (T * n) ≤ 2 ^ (T * (n + 1)) := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left T (Nat.le_succ n))
  change (SchwartzMap.fourierTransformCLM ℂ
    (lowpassSchwartzKernel _ _ - lowpassSchwartzKernel _ _)) ξ = _
  rw [map_sub, sub_apply]
  simp only [SchwartzMap.fourierTransformCLM_apply]
  rcases hξ with hξ | hξ
  · rw [fourier_lowpassSchwartzKernel_eq_one _ _ (hξ.trans (by linarith)),
      fourier_lowpassSchwartzKernel_eq_one _ _ hξ, sub_self]
  · rw [fourier_lowpassSchwartzKernel_eq_zero _ _ hξ,
      fourier_lowpassSchwartzKernel_eq_zero _ _ (le_trans (by linarith) hξ), sub_self]

/-- Positive integer block sizes give scales tending to infinity. -/
theorem tendsto_dyadic_blockScale {T : ℕ} (hT : 0 < T) :
    Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (T * n)) atTop atTop := by
  have hbase : (1 : ℝ) < 2 ^ T := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hT)
  simpa only [pow_mul] using tendsto_pow_atTop_atTop_of_one_lt hbase

/-- The full annulus has a uniform first norm, independent of both the scale and block size. -/
theorem integral_norm_dyadicAnnularKernel_le (T n : ℕ) :
    (∫ x, ‖dyadicAnnularKernel T n x‖) ≤ 2 * ∫ x, ‖unitReproducingKernel x‖ := by
  calc
    _ ≤ ∫ x, ‖lowpassSchwartzKernel (2 ^ (T * (n + 1))) (by positivity) x‖ +
        ‖lowpassSchwartzKernel (2 ^ (T * n)) (by positivity) x‖ := by
      apply integral_mono (dyadicAnnularKernel T n).integrable.norm
        ((lowpassSchwartzKernel _ _).integrable.norm.add
          (lowpassSchwartzKernel _ _).integrable.norm)
      intro x
      exact norm_sub_le _ _
    _ = _ := by
      rw [integral_add (lowpassSchwartzKernel _ _).integrable.norm
        (lowpassSchwartzKernel _ _).integrable.norm,
        integral_norm_lowpassSchwartzKernel, integral_norm_lowpassSchwartzKernel]
      ring

/-- The low-frequency term and all annuli through level `N-1` telescope exactly. -/
theorem sum_dyadicAnnularKernel (T N : ℕ) :
    lowpassSchwartzKernel 1 (by norm_num) + ∑ n ∈ Finset.range N, dyadicAnnularKernel T n =
      lowpassSchwartzKernel (2 ^ (T * N)) (by positivity) := by
  have h := Finset.sum_range_sub
    (fun n ↦ lowpassSchwartzKernel (2 ^ (T * n)) (by positivity)) N
  simpa [dyadicAnnularKernel] using congrArg
    (fun f ↦ lowpassSchwartzKernel 1 (by norm_num) + f) h

end FalconerPacking
