/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.NormalizedSpatialStrip
public import FalconerPacking.RescaledSchwartzKernel

/-!
# Actual anisotropic Fourier decay of spatial strip cutoffs

An exact affine change of variables transfers the uniform normalized Schwartz estimates
to the physical cutoff. Transverse frequency is measured in units of inverse strip width;
longitudinal frequency retains unit scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- A physical translation gives its exact unit Fourier phase. -/
theorem schwartz_fourier_translate_apply
    (F : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (z ξ : EuclideanSpace ℝ (Fin 2)) :
    (𝓕 (SchwartzMap.compSubConstCLM ℂ z F)) ξ =
      Real.fourierChar (-⟪z, ξ⟫) • (𝓕 F) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [SchwartzMap.compSubConstCLM_apply]
  calc
    _ = ∫ x, Real.fourierChar (-⟪x + z, ξ⟫) • F x := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun x ↦ Real.fourierChar (-⟪x, ξ⟫) • F (x - z)) z).symm
    _ = Real.fourierChar (-⟪z, ξ⟫) • ∫ x, Real.fourierChar (-⟪x, ξ⟫) • F x := by
      simp only [inner_add_left, neg_add, Real.fourierChar.map_add_eq_mul, mul_smul]
      simp only [Circle.smul_def]
      rw [← integral_smul]
      apply integral_congr_ae
      exact ae_of_all _ fun _ ↦ smul_comm _ _ _
    _ = _ := by rw [SchwartzMap.fourier_coe, Real.fourier_eq]

/-- Exact Schwartz-space rescaling of the physical spatial cutoff. -/
theorem spatialStripCutoff_eq_rescaled
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2)) (he : ∀ x, ⟪e, x⟫ = O x 0)
    (w : ℝ) (hw : 0 < w) (j : ℤ) :
    spatialStripCutoff χ hχ w e j = w •
      SchwartzMap.compSubConstCLM ℂ (spatialStripCenter O w j)
        (rescaledSchwartzKernel (orientedRectangleDilation O w 1 hw zero_lt_one)
          (normalizedSpatialStrip χ hχ O w hw j)) := by
  ext x
  rw [spatialStripCutoff_eq_normalized χ hχ O e he w hw j x]
  simp only [smul_apply, SchwartzMap.compSubConstCLM_apply,
    rescaledSchwartzKernel_apply, smul_smul, orientedRectangleDilation_abs_det,
    mul_one, mul_inv_cancel₀ hw.ne', one_smul, spatialStripSynthesis,
    ContinuousLinearEquiv.symm_symm]

/-- The actual Fourier modulus, including its exact transverse Jacobian. -/
theorem norm_fourier_spatialStripCutoff
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2)) (he : ∀ x, ⟪e, x⟫ = O x 0)
    (w : ℝ) (hw : 0 < w) (j : ℤ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖(𝓕 (spatialStripCutoff χ hχ w e j)) ξ‖ =
      w * ‖(𝓕 (normalizedSpatialStrip χ hχ O w hw j))
        (WithLp.toLp 2 ![w * (O ξ) 0, (O ξ) 1])‖ := by
  rw [spatialStripCutoff_eq_rescaled χ hχ O e he w hw j, fourier_smul]
  simp only [smul_apply]
  rw [schwartz_fourier_translate_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hw,
    Circle.norm_smul, fourier_rescaledSchwartzKernel, orientedRectangleDilation_dual]
  simp only [one_mul]

/-- Rapid tails of the true cutoff Fourier transform in the correct anisotropic metric. -/
theorem exists_spatialStripCutoff_fourier_decay
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (e : EuclideanSpace ℝ (Fin 2)), (∀ x, ⟪e, x⟫ = O x 0) →
        ∀ w : ℝ, 0 < w → w ≤ 1 → ∀ (j : ℤ) (ξ : EuclideanSpace ℝ (Fin 2)),
          ‖(𝓕 (spatialStripCutoff χ hχ w e j)) ξ‖ ≤
            w * C / (1 + ‖(WithLp.toLp 2 ![w * (O ξ) 0, (O ξ) 1] :
              EuclideanSpace ℝ (Fin 2))‖) ^ m := by
  obtain ⟨C, hC, hc⟩ := exists_normalizedSpatialStrip_fourier_decay χ hχ m
  refine ⟨C, hC, fun O e he w hw hw₁ j ξ ↦ ?_⟩
  rw [norm_fourier_spatialStripCutoff χ hχ O e he w hw j]
  exact (mul_le_mul_of_nonneg_left (hc O w hw hw₁ j _) hw.le).trans_eq (by ring)

end FalconerPacking
