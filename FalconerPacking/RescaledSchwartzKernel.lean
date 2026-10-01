/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AnisotropicSchwartzKernel

/-!
# Exact linear rescaling of arbitrary Schwartz kernels

The determinant normalization preserves the actual first norm, including on transformed
measurable sets. The dual symbol identity identifies these constructed kernels with the
actual inverse Fourier transform of any corresponding rescaled multiplier.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- An arbitrary actual Schwartz kernel rescaled by a linear equivalence and its Jacobian. -/
def rescaledSchwartzKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  |A.toLinearEquiv.toLinearMap.det| • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A K

@[simp]
theorem rescaledSchwartzKernel_apply
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    rescaledSchwartzKernel A K x = |A.toLinearEquiv.toLinearMap.det| • K (A x) := rfl

/-- The exact first norm on every transformed measurable set. -/
theorem setLIntegral_enorm_rescaledSchwartzKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) :
    (∫⁻ x in A ⁻¹' S, ‖rescaledSchwartzKernel A K x‖ₑ) = ∫⁻ x in S, ‖K x‖ₑ := by
  have hD : 0 < |A.toLinearEquiv.toLinearMap.det| :=
    abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  rw [← lintegral_indicator (hS.preimage A.continuous.measurable), ← lintegral_indicator hS]
  have he (x : EuclideanSpace ℝ (Fin 2)) :
      (A ⁻¹' S).indicator (fun x ↦ ‖rescaledSchwartzKernel A K x‖ₑ) x =
        ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det| *
          S.indicator (fun z ↦ ‖K z‖ₑ) (A x) := by
    by_cases hx : A x ∈ S
    · rw [indicator_of_mem (show x ∈ A ⁻¹' S from hx), indicator_of_mem hx]
      simp only [rescaledSchwartzKernel_apply, enorm_smul, Real.enorm_eq_ofReal_abs, abs_abs]
    · rw [indicator_of_notMem (show x ∉ A ⁻¹' S from hx), indicator_of_notMem hx, mul_zero]
  simp_rw [he]
  have hm : Measurable (fun x ↦ S.indicator (fun z ↦ ‖K z‖ₑ) (A x)) :=
    ((K.continuous.measurable.enorm).indicator hS).comp A.continuous.measurable
  rw [lintegral_const_mul _ hm, lintegral_comp_continuousLinearEquiv_det]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne',
    ENNReal.ofReal_one, one_mul]

/-- Whole-space first norms are exactly unchanged by determinant-normalized rescaling. -/
theorem lintegral_enorm_rescaledSchwartzKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫⁻ x, ‖rescaledSchwartzKernel A K x‖ₑ) = ∫⁻ x, ‖K x‖ₑ := by
  simpa only [preimage_univ, Measure.restrict_univ] using
    setLIntegral_enorm_rescaledSchwartzKernel A K MeasurableSet.univ

/-- Exact Fourier transformation of the constructed kernel. -/
theorem fourier_rescaledSchwartzKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    (𝓕 (rescaledSchwartzKernel A K) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ =
      (𝓕 K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
        (A.symm.toContinuousLinearMap.adjoint ξ) := by
  have hD : 0 < |A.toLinearEquiv.toLinearMap.det| :=
    abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  let g (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
    𝐞 (-⟪x, A.symm.toContinuousLinearMap.adjoint ξ⟫) • K x
  have hinner (x : EuclideanSpace ℝ (Fin 2)) :
      ⟪A x, A.symm.toContinuousLinearMap.adjoint ξ⟫ = ⟪x, ξ⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp
  calc
    _ = |A.toLinearEquiv.toLinearMap.det| • ∫ x, g (A x) := by
      rw [SchwartzMap.fourier_coe, Real.fourier_eq, ← integral_smul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [g]
      rw [rescaledSchwartzKernel_apply, hinner, smul_comm]
    _ = ∫ x, g x := by
      rw [integral_comp_continuousLinearEquiv_det, smul_smul,
        mul_inv_cancel₀ hD.ne', one_smul]
    _ = _ := by rw [SchwartzMap.fourier_coe, Real.fourier_eq]

/-- An actual dual symbol identity identifies the inverse transform, rather than merely
providing a candidate kernel with convenient estimates. -/
theorem fourierInv_eq_rescaledSchwartzKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (ψ F : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (he : ∀ ξ, ψ ξ = F (A.symm.toContinuousLinearMap.adjoint ξ)) :
    (𝓕⁻ ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) =
      rescaledSchwartzKernel A (𝓕⁻ F) := by
  have hf : (𝓕 (rescaledSchwartzKernel A (𝓕⁻ F)) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) = ψ := by
    ext ξ
    rw [fourier_rescaledSchwartzKernel, fourier_fourierInv_eq, he]
  simpa only [fourierInv_fourier_eq] using congrArg
    (fun f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ ↦ 𝓕⁻ f) hf.symm

end FalconerPacking
