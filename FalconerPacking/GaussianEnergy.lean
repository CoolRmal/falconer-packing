/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian Fourier energy

The Gaussian identity turns a positive measure's squared Fourier transform into a positive
spatial kernel. The characteristic-function convention has phase `exp(i ⟪x,ξ⟫)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ComplexConjugate
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- The planar Gaussian integral against one character. -/
theorem integral_gaussian_mul_character {b : ℝ} (hb : 0 < b)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2),
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) * Complex.exp (⟪x, ξ⟫ * Complex.I) =
      (Real.pi / b : ℝ) * Complex.exp (-(‖x‖ ^ 2 / (4 * b) : ℝ)) := by
  simp_rw [← Complex.exp_add, mul_comm (⟪x, _⟫ : ℂ) Complex.I]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by exact hb)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  norm_num
  ring_nf
  simp

/-- A Gaussian dominates the joint character kernel, justifying the interchange of integrals. -/
theorem integrable_gaussian_character_kernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      Complex.exp (-(b : ℂ) * ‖p.1‖ ^ 2) * Complex.exp (⟪p.2, p.1⟫ * Complex.I))
      (volume.prod μ) := by
  have hg : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2)) volume := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by exact hb : 0 < (b : ℂ).re) 0 (0 : EuclideanSpace ℝ (Fin 2))
  apply (hg.comp_fst μ).mono (by fun_prop)
  exact Filter.Eventually.of_forall fun p ↦ by simp

/-- Integrating a characteristic function against a Gaussian gives its spatial Gaussian mean. -/
theorem integral_gaussian_mul_charFun
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2),
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) * charFun μ ξ =
      (Real.pi / b : ℝ) *
        ∫ x, Complex.exp (-(‖x‖ ^ 2 / (4 * b) : ℝ)) ∂μ := by
  simp_rw [charFun_apply, ← integral_const_mul]
  rw [integral_integral_swap (integrable_gaussian_character_kernel μ hb)]
  simp_rw [integral_gaussian_mul_character hb]

/-- The Fourier transform of the difference law is the squared modulus of the original
characteristic function. -/
theorem charFun_difference_eq_norm_sq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    charFun ((μ.prod μ).map (fun p ↦ p.1 - p.2)) ξ = (‖charFun μ ξ‖ ^ 2 : ℝ) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hphase (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
      Complex.exp (⟪p.1 - p.2, ξ⟫ * Complex.I) =
        Complex.exp (⟪p.1, ξ⟫ * Complex.I) *
          Complex.exp (⟪p.2, -ξ⟫ * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_sub_left, inner_neg_right, Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  simp_rw [hphase]
  rw [integral_prod_mul (fun x : EuclideanSpace ℝ (Fin 2) ↦
    Complex.exp (⟪x, ξ⟫ * Complex.I)) (fun x : EuclideanSpace ℝ (Fin 2) ↦
    Complex.exp (⟪x, -ξ⟫ * Complex.I))]
  change charFun μ ξ * charFun μ (-ξ) = _
  rw [charFun_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Exact planar Gaussian Fourier energy identity, with its positive spatial kernel. -/
theorem integral_gaussian_charFun_norm_sq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2), Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 =
      Real.pi / b * ∫ p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        Real.exp (-(‖p.1 - p.2‖ ^ 2 / (4 * b))) ∂μ.prod μ := by
  have h := integral_gaussian_mul_charFun
    ((μ.prod μ).map (fun p ↦ p.1 - p.2)) hb
  simp_rw [charFun_difference_eq_norm_sq] at h
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  have hexp (ξ : EuclideanSpace ℝ (Fin 2)) :
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) = (Real.exp (-b * ‖ξ‖ ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  simp_rw [hexp] at h
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    integral_complex_ofReal] at h
  exact Complex.ofReal_inj.mp h

end FalconerPacking
