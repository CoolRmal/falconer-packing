/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CapFrequencyRescaling

/-!
# The fixed radial factor of a rescaled dyadic cap

After rescaling, the radial multiplier is the fixed first annulus composed with a linear
contraction. Consequently all its derivatives have bounds independent of the annulus index.
-/

@[expose] public section

noncomputable section

open Set SchwartzMap FourierTransform
open scoped ContDiff

namespace FalconerPacking

/-- The remaining contraction after the full annular scale has been removed. -/
def capUnitRescaling (T n N j : ℕ) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (euclideanCoordinateDilation ![(Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹, 1] (by
    intro i
    fin_cases i <;> simp)).trans
    (circleCapFrame (angularGridPoint N j)).symm.toContinuousLinearEquiv

theorem capUnitRescaling_apply (T n N j : ℕ) (z : EuclideanSpace ℝ (Fin 2)) :
    capUnitRescaling T n N j z = (circleCapFrame (angularGridPoint N j)).symm
      (WithLp.toLp 2 ![(Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹ * z 0, z 1]) := by
  simp only [capUnitRescaling, ContinuousLinearEquiv.trans_apply]
  apply congrArg (circleCapFrame (angularGridPoint N j)).symm
  ext i
  fin_cases i <;> simp [euclideanCoordinateDilation_apply]

/-- The full frequency map is exactly the annular scale times its unit contraction. -/
theorem capFrequencyRescaling_eq_smul (T n N j : ℕ) (z : EuclideanSpace ℝ (Fin 2)) :
    capFrequencyRescaling T n N j z = (2 : ℝ) ^ (T * n) • capUnitRescaling T n N j z := by
  apply (circleCapFrame (angularGridPoint N j)).injective
  rw [map_smul, capUnitRescaling_apply, LinearIsometryEquiv.apply_symm_apply]
  ext i
  fin_cases i
  · change circleCapFrame (angularGridPoint N j) (capFrequencyRescaling T n N j z) 0 =
      (2 : ℝ) ^ (T * n) * ((Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹ * z 0)
    rw [capFrequencyRescaling_frame_zero]
    have hR : 0 < (2 : ℝ) ^ (T * n) := by positivity
    have hs := Real.sq_sqrt hR.le
    field_simp
    rw [hs]
  · change circleCapFrame (angularGridPoint N j) (capFrequencyRescaling T n N j z) 1 =
      (2 : ℝ) ^ (T * n) * z 1
    exact capFrequencyRescaling_frame_one T n N j z

/-- The remaining frequency map is a contraction at every dyadic scale. -/
theorem capUnitRescaling_norm_le (T n N j : ℕ) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖capUnitRescaling T n N j z‖ ≤ ‖z‖ := by
  rw [capUnitRescaling_apply, LinearIsometryEquiv.norm_map]
  have hR : 1 ≤ (2 : ℝ) ^ (T * n) := one_le_pow₀ (by norm_num)
  have hε : (Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact Real.one_le_sqrt.mpr hR)
  have hε₀ : 0 ≤ (Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹ := by positivity
  have hs := EuclideanSpace.real_norm_sq_eq z
  rw [Fin.sum_univ_two] at hs
  have ht := EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 ![(Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹ * z 0, z 1])
  rw [Fin.sum_univ_two] at ht
  change _ = ((Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹ * z 0) ^ 2 + (z 1) ^ 2 at ht
  have hp : ((Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹) ^ 2 * (z 0) ^ 2 ≤ (z 0) ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hε₀ hε)
  nlinarith [norm_nonneg z, norm_nonneg
    (WithLp.toLp 2 ![(Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹ * z 0, z 1])]

theorem capUnitRescaling_opNorm_le (T n N j : ℕ) :
    ‖(capUnitRescaling T n N j).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  change ‖capUnitRescaling T n N j z‖ ≤ 1 * ‖z‖
  simpa only [one_mul] using capUnitRescaling_norm_le T n N j z

/-- The dyadic annular multiplier is a rescaling of the first annulus. -/
theorem fourier_dyadicAnnularKernel_scale (T n : ℕ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    (𝓕 (dyadicAnnularKernel T n) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
      ((2 : ℝ) ^ (T * n) • ξ) =
      (𝓕 (dyadicAnnularKernel T 0) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ := by
  rw [fourier_dyadicAnnularKernel, fourier_dyadicAnnularKernel]
  simp only [Nat.zero_add, Nat.mul_one, Nat.mul_zero, pow_zero, inv_one, one_smul,
    smul_smul, Nat.mul_add, pow_add, mul_inv_rev]
  have hR : (2 : ℝ) ^ (T * n) ≠ 0 := by positivity
  simp [hR]

/-- The angular weights are homogeneous of degree zero at positive scalings. -/
theorem angularCapWeight_smul_pos (N : ℕ) (hN : 0 < N) (j : ℕ) {r : ℝ} (hr : 0 < r)
    (ξ : EuclideanSpace ℝ (Fin 2)) : angularCapWeight N hN j (r • ξ) =
      angularCapWeight N hN j ξ := by
  have he : ‖r • ξ‖⁻¹ • (r • ξ) = ‖ξ‖⁻¹ • ξ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev, smul_smul]
    simp [hr.ne']
  simp only [angularCapWeight, angularCapDenominator, he]

/-- The rescaled symbol is the actual angular weight times one fixed contracted radial factor. -/
theorem rescaledDyadicAngularCap_factor (T n N : ℕ) (hN : 0 < N) (j : ℕ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    rescaledDyadicAngularCap T n N hN j z =
      angularCapWeight N hN j (capUnitRescaling T n N j z) •
        (𝓕 (dyadicAnnularKernel T 0) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
          (capUnitRescaling T n N j z) := by
  rw [rescaledDyadicAngularCap_apply]
  change angularCapWeight N hN j (capFrequencyRescaling T n N j z) •
    (𝓕 (dyadicAnnularKernel T n) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
      (capFrequencyRescaling T n N j z) = _
  rw [capFrequencyRescaling_eq_smul, angularCapWeight_smul_pos N hN j (by positivity),
    fourier_dyadicAnnularKernel_scale]

/-- The radial factor's derivative constants are independent of the annulus and cap indices. -/
theorem rescaledAnnularFactor_derivative_bound (T m : ℕ) (n N j : ℕ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    ‖iteratedFDeriv ℝ m
      (fun w ↦ (𝓕 (dyadicAnnularKernel T 0) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
        (capUnitRescaling T n N j w)) z‖ ≤
      SchwartzMap.seminorm ℂ 0 m (𝓕 (dyadicAnnularKernel T 0)) := by
  let f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ := 𝓕 (dyadicAnnularKernel T 0)
  let L := (capUnitRescaling T n N j).toContinuousLinearMap
  change ‖iteratedFDeriv ℝ m (f ∘ L) z‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (f.smooth ⊤) _ (mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f (L z)‖ * ‖L‖ ^ m := by
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ m f (L z)) (fun _ ↦ L)
    _ ≤ ‖iteratedFDeriv ℝ m f (L z)‖ := mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (capUnitRescaling_opNorm_le T n N j))
    _ ≤ _ := f.norm_iteratedFDeriv_le_seminorm ℂ m _

end FalconerPacking
