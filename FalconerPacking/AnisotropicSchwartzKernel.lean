/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SchwartzReproducingKernel
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Anisotropically rescaled Schwartz kernels

Linear changes of variables produce actual reproducing kernels with a uniform L¹ norm
and rapid decay in the transformed spatial coordinate.
-/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal Convolution RealInnerProductSpace FourierTransform

namespace FalconerPacking

/-- Change of variables for a continuous linear equivalence, with its exact Jacobian. -/
theorem integral_comp_continuousLinearEquiv_det
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) :
    (∫ x, f (A x)) = |A.toLinearEquiv.toLinearMap.det|⁻¹ • ∫ x, f x := by
  have hdet : A.toLinearEquiv.toLinearMap.det ≠ 0 :=
    A.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : Measure.map A volume =
      ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det|⁻¹ • volume := by
    convert Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet using 1 <;>
      simp [abs_inv]
  have hchange := A.toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  change (∫ x, f x ∂Measure.map A volume) = ∫ x, f (A x) at hchange
  rw [← hchange, hmap, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ |A.toLinearEquiv.toLinearMap.det|⁻¹)]

/-- The positive-integral version of the same linear change of variables. -/
theorem lintegral_comp_continuousLinearEquiv_det
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    (∫⁻ x, f (A x)) = ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det|⁻¹ * ∫⁻ x, f x := by
  have hdet : A.toLinearEquiv.toLinearMap.det ≠ 0 :=
    A.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : Measure.map A volume =
      ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det|⁻¹ • volume := by
    convert Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet using 1 <;>
      simp [abs_inv]
  have hchange := A.toHomeomorph.measurableEmbedding.lintegral_map (μ := volume) f
  change (∫⁻ x, f x ∂Measure.map A volume) = ∫⁻ x, f (A x) at hchange
  rw [← hchange, hmap, lintegral_smul_measure]
  rfl

/-- The fixed inverse Fourier cutoff, rescaled with the exact Jacobian factor. -/
def anisotropicReproducingKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  |A.toLinearEquiv.toLinearMap.det| •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A unitReproducingKernel)

/-- The rescaling formula holds pointwise for the constructed Schwartz function. -/
theorem anisotropicReproducingKernel_apply
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) :
    anisotropicReproducingKernel A x =
      |A.toLinearEquiv.toLinearMap.det| • unitReproducingKernel (A x) := rfl

/-- Every rescaled kernel has exactly the L¹ norm of the fixed kernel. -/
theorem anisotropicReproducingKernel_lintegral_enorm
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ x, ‖anisotropicReproducingKernel A x‖ₑ) =
      ∫⁻ x, ‖unitReproducingKernel x‖ₑ := by
  have hdet : A.toLinearEquiv.toLinearMap.det ≠ 0 :=
    A.toLinearEquiv.isUnit_det'.ne_zero
  have hD : 0 < |A.toLinearEquiv.toLinearMap.det| := abs_pos.mpr hdet
  simp only [anisotropicReproducingKernel_apply, enorm_smul, Real.enorm_eq_ofReal_abs,
    abs_abs]
  rw [lintegral_const_mul _ (f := fun x ↦ ‖unitReproducingKernel (A x)‖ₑ)
    (unitReproducingKernel.continuous.measurable.comp A.continuous.measurable).enorm,
    lintegral_comp_continuousLinearEquiv_det A (fun y ↦ ‖unitReproducingKernel y‖ₑ)]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne',
    ENNReal.ofReal_one, one_mul]

/-- Rapid anisotropic decay has constants depending only on the fixed cutoff and the order. -/
theorem anisotropicReproducingKernel_decay (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) x,
        ‖anisotropicReproducingKernel A x‖ ≤
          |A.toLinearEquiv.toLinearMap.det| * C / (1 + ‖A x‖) ^ m := by
  let C := 2 ^ m * (Finset.Iic (m, 0)).sup
    (fun p ↦ SchwartzMap.seminorm ℝ p.1 p.2) unitReproducingKernel
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro A x
  have hdecay : (1 + ‖A x‖) ^ m * ‖unitReproducingKernel (A x)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0))
        le_rfl le_rfl unitReproducingKernel (A x)
  have hbase : ‖unitReproducingKernel (A x)‖ ≤ (|C| + 1) / (1 + ‖A x‖) ^ m := by
    apply (le_div_iff₀ (by positivity : 0 < (1 + ‖A x‖) ^ m)).mpr
    calc
      _ ≤ C := by simpa only [mul_comm] using hdecay
      _ ≤ |C| + 1 := by linarith [le_abs_self C]
  rw [anisotropicReproducingKernel_apply, norm_smul, Real.norm_eq_abs, abs_abs]
  exact (mul_le_mul_of_nonneg_left hbase (abs_nonneg _)).trans_eq (by ring)

/-- The Fourier transform of the rescaled kernel is the fixed cutoff at the dual coordinate. -/
theorem fourier_anisotropicReproducingKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    (𝓕 (anisotropicReproducingKernel A) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ =
      unitFrequencyCutoff (A.symm.toContinuousLinearMap.adjoint ξ) := by
  have hdet : A.toLinearEquiv.toLinearMap.det ≠ 0 :=
    A.toLinearEquiv.isUnit_det'.ne_zero
  have hD : 0 < |A.toLinearEquiv.toLinearMap.det| := abs_pos.mpr hdet
  let g : EuclideanSpace ℝ (Fin 2) → ℂ := fun y ↦
    𝐞 (-⟪y, A.symm.toContinuousLinearMap.adjoint ξ⟫) • unitReproducingKernel y
  have hinner (x : EuclideanSpace ℝ (Fin 2)) :
      ⟪A x, A.symm.toContinuousLinearMap.adjoint ξ⟫ = ⟪x, ξ⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp
  calc
    _ = |A.toLinearEquiv.toLinearMap.det| • ∫ x, g (A x) := by
      rw [SchwartzMap.fourier_coe, Real.fourier_eq, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [g]
      rw [anisotropicReproducingKernel_apply, hinner, smul_comm]
    _ = |A.toLinearEquiv.toLinearMap.det| •
        (|A.toLinearEquiv.toLinearMap.det|⁻¹ • ∫ x, g x) := by
      rw [integral_comp_continuousLinearEquiv_det]
    _ = ∫ x, g x := by rw [smul_smul, mul_inv_cancel₀ hD.ne', one_smul]
    _ = _ := by
      change (𝓕 (unitReproducingKernel : EuclideanSpace ℝ (Fin 2) → ℂ))
        (A.symm.toContinuousLinearMap.adjoint ξ) = _
      rw [← SchwartzMap.fourier_coe]
      simp only [unitReproducingKernel, fourier_fourierInv_eq]

/-- The rescaled kernel reproduces the Fourier rectangle in its dual coordinates. -/
theorem anisotropicReproducingKernel_reproduces
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hf : ∀ ξ ∈ Function.support
      (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
      ∀ i, |(A.symm.toContinuousLinearMap.adjoint ξ) i| ≤ 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ] anisotropicReproducingKernel A) x = f x := by
  have h := schwartz_convolution_fourierInv_cutoff f
    (𝓕 (anisotropicReproducingKernel A)) (fun ξ hξ ↦ ?_) x
  · simpa only [fourierInv_fourier_eq] using h
  · rw [fourier_anisotropicReproducingKernel]
    exact unitFrequencyCutoff_eq_one (hf ξ hξ)

/-- Translating the cutoff in frequency modulates its inverse transform by a unit phase. -/
theorem schwartz_fourierInv_translate_apply
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (ξ₀ x : EuclideanSpace ℝ (Fin 2)) :
    (𝓕⁻ (SchwartzMap.compSubConstCLM ℂ ξ₀ χ) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x =
      𝐞 ⟪ξ₀, x⟫ • (𝓕⁻ χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp only [SchwartzMap.compSubConstCLM_apply]
  calc
    _ = ∫ y, 𝐞 ⟪y + ξ₀, x⟫ • χ y := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun y ↦ 𝐞 ⟪y, x⟫ • χ (y - ξ₀)) ξ₀).symm
    _ = 𝐞 ⟪ξ₀, x⟫ • ∫ y, 𝐞 ⟪y, x⟫ • χ y := by
      simp only [inner_add_left, Real.fourierChar.map_add_eq_mul, mul_smul]
      simp only [Circle.smul_def]
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with y
      exact smul_comm _ _ _
    _ = _ := by rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]

/-- A translated Fourier rectangle has this explicitly constructed Schwartz kernel. -/
def shiftedAnisotropicReproducingKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (ξ₀ : EuclideanSpace ℝ (Fin 2)) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  𝓕⁻ (SchwartzMap.compSubConstCLM ℂ ξ₀ (𝓕 (anisotropicReproducingKernel A)))

/-- Frequency translation changes the constructed kernel only by its explicit phase. -/
theorem shiftedAnisotropicReproducingKernel_apply
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (ξ₀ x : EuclideanSpace ℝ (Fin 2)) :
    shiftedAnisotropicReproducingKernel A ξ₀ x =
      𝐞 ⟪ξ₀, x⟫ • anisotropicReproducingKernel A x := by
  rw [shiftedAnisotropicReproducingKernel, schwartz_fourierInv_translate_apply,
    fourierInv_fourier_eq]

/-- In particular the frequency center has no effect on the pointwise modulus. -/
theorem norm_shiftedAnisotropicReproducingKernel
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (ξ₀ x : EuclideanSpace ℝ (Fin 2)) :
    ‖shiftedAnisotropicReproducingKernel A ξ₀ x‖ =
      ‖anisotropicReproducingKernel A x‖ := by
  rw [shiftedAnisotropicReproducingKernel_apply, Circle.norm_smul]

/-- The actual shifted kernel reproduces its full translated Fourier rectangle. -/
theorem shiftedAnisotropicReproducingKernel_reproduces
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (ξ₀ : EuclideanSpace ℝ (Fin 2))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hf : ∀ ξ ∈ Function.support
      (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
      ∀ i, |(A.symm.toContinuousLinearMap.adjoint (ξ - ξ₀)) i| ≤ 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ] shiftedAnisotropicReproducingKernel A ξ₀) x =
      f x := by
  apply schwartz_convolution_fourierInv_cutoff
  intro ξ hξ
  rw [SchwartzMap.compSubConstCLM_apply, fourier_anisotropicReproducingKernel]
  exact unitFrequencyCutoff_eq_one (hf ξ hξ)

/-- The L¹ norm is uniform in both the linear scaling and the Fourier center. -/
theorem shiftedAnisotropicReproducingKernel_lintegral_enorm
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (ξ₀ : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ x, ‖shiftedAnisotropicReproducingKernel A ξ₀ x‖ₑ) =
      ∫⁻ x, ‖unitReproducingKernel x‖ₑ := by
  simp only [← ofReal_norm, norm_shiftedAnisotropicReproducingKernel]
  simpa only [ofReal_norm] using anisotropicReproducingKernel_lintegral_enorm A

/-- Uniform rapid decay survives arbitrary frequency translation. -/
theorem shiftedAnisotropicReproducingKernel_decay (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) ξ₀ x,
        ‖shiftedAnisotropicReproducingKernel A ξ₀ x‖ ≤
          |A.toLinearEquiv.toLinearMap.det| * C / (1 + ‖A x‖) ^ m := by
  obtain ⟨C, hC, hdecay⟩ := anisotropicReproducingKernel_decay m
  exact ⟨C, hC, fun A ξ₀ x ↦ by
    simpa only [norm_shiftedAnisotropicReproducingKernel] using hdecay A x⟩

end FalconerPacking
