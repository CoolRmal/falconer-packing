/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.FourierDensity
public import FalconerPacking.GaussianMellin
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# One-dimensional Fourier representation of Riesz energy

The Gaussian identity is integrated against its positive Mellin weight. Extended nonnegative
integrals retain the diagonal singularity rather than assigning it the real-number value zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter ComplexConjugate
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Riesz energy on the real line, with an infinite kernel on the diagonal for positive t. -/
def rieszEnergy1D (μ : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal (dist x y) ^ (-t) ∂μ ∂μ

/-- The real Gaussian integral against one character, in characteristic-function normalization. -/
theorem integral_gaussian_mul_character_real {b : ℝ} (hb : 0 < b) (x : ℝ) :
    ∫ ξ : ℝ, Complex.exp (-(b : ℂ) * ξ ^ 2) * Complex.exp ((x * ξ : ℝ) * Complex.I) =
      ((Real.pi / b) ^ (1 / 2 : ℝ) : ℝ) *
        Complex.exp (-(x ^ 2 / (4 * b) : ℝ)) := by
  have h := fourierIntegral_gaussian (b := (b : ℂ)) (by exact hb) (x : ℂ)
  have hp (ξ : ℝ) : Complex.exp (-(b : ℂ) * ξ ^ 2) *
      Complex.exp ((x * ξ : ℝ) * Complex.I) =
      Complex.exp (Complex.I * (x : ℂ) * ξ) * Complex.exp (-(b : ℂ) * ξ ^ 2) := by
    simp only [Complex.ofReal_mul, mul_comm, mul_left_comm]
  simp_rw [hp]
  rw [h]
  have hpow : (Real.pi / (b : ℂ)) ^ (1 / 2 : ℂ) =
      ((Real.pi / b) ^ (1 / 2 : ℝ) : ℝ) := by
    convert (Complex.ofReal_cpow (x := Real.pi / b) (y := 1 / 2) (by positivity)).symm using 1
    norm_num
  rw [hpow]
  congr 2
  push_cast
  ring

/-- The difference law has characteristic function equal to the squared modulus. -/
theorem charFun_difference_real_eq_norm_sq
    (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    charFun ((μ.prod μ).map (fun p ↦ p.1 - p.2)) ξ = (‖charFun μ ξ‖ ^ 2 : ℝ) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hp (p : ℝ × ℝ) : Complex.exp (⟪p.1 - p.2, ξ⟫ * Complex.I) =
      Complex.exp (⟪p.1, ξ⟫ * Complex.I) *
        Complex.exp (⟪p.2, -ξ⟫ * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_sub_left, inner_neg_right, Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  simp_rw [hp]
  rw [integral_prod_mul (fun x : ℝ ↦ Complex.exp (⟪x, ξ⟫ * Complex.I))
    (fun x : ℝ ↦ Complex.exp (⟪x, -ξ⟫ * Complex.I))]
  change charFun μ ξ * charFun μ (-ξ) = _
  rw [charFun_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Gaussian duality for a finite real measure. -/
theorem integral_gaussian_mul_charFun_real
    (μ : Measure ℝ) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) :
    ∫ ξ : ℝ, Complex.exp (-(b : ℂ) * ξ ^ 2) * charFun μ ξ =
      ((Real.pi / b) ^ (1 / 2 : ℝ) : ℝ) *
        ∫ x, Complex.exp (-(x ^ 2 / (4 * b) : ℝ)) ∂μ := by
  have hg : Integrable (fun ξ : ℝ ↦ Complex.exp (-(b : ℂ) * ξ ^ 2)) volume := by
    simpa using integrable_cexp_quadratic (b := (b : ℂ)) (by exact hb) 0 0
  have hint : Integrable (fun p : ℝ × ℝ ↦
      Complex.exp (-(b : ℂ) * p.1 ^ 2) * Complex.exp ((p.1 * p.2 : ℝ) * Complex.I))
      (volume.prod μ) := by
    apply (hg.comp_fst μ).mono (by fun_prop)
    exact Eventually.of_forall fun p ↦ by
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  simp_rw [charFun_apply_real, ← integral_const_mul]
  rw [integral_integral_swap (by simpa only [Complex.ofReal_mul, Function.uncurry_def] using hint)]
  have hp (x ξ : ℝ) : (ξ : ℂ) * x * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp_rw [hp, integral_gaussian_mul_character_real hb]

/-- The positive one-dimensional Gaussian Fourier energy identity. -/
theorem integral_gaussian_charFun_norm_sq_real
    (μ : Measure ℝ) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) :
    ∫ ξ : ℝ, Real.exp (-b * ξ ^ 2) * ‖charFun μ ξ‖ ^ 2 =
      (Real.pi / b) ^ (1 / 2 : ℝ) *
        ∫ p : ℝ × ℝ, Real.exp (-((p.1 - p.2) ^ 2 / (4 * b))) ∂μ.prod μ := by
  have h := integral_gaussian_mul_charFun_real
    ((μ.prod μ).map (fun p ↦ p.1 - p.2)) hb
  simp_rw [charFun_difference_real_eq_norm_sq] at h
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  have hexp (ξ : ℝ) : Complex.exp (-(b : ℂ) * ξ ^ 2) =
      (Real.exp (-b * ξ ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  simp_rw [hexp] at h
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    integral_complex_ofReal] at h
  exact Complex.ofReal_inj.mp h

/-- Gaussian Fourier energy is an extended nonnegative integral identity as well. -/
theorem lintegral_gaussian_charFun_norm_sq_real
    (μ : Measure ℝ) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) :
    ∫⁻ ξ : ℝ, ENNReal.ofReal (Real.exp (-b * |ξ| ^ 2)) *
      ENNReal.ofReal (‖charFun μ ξ‖ ^ 2) =
        ENNReal.ofReal ((Real.pi / b) ^ (1 / 2 : ℝ)) *
          ∫⁻ p : ℝ × ℝ, ENNReal.ofReal
            (Real.exp (-(dist p.1 p.2 ^ 2 / (4 * b)))) ∂μ.prod μ := by
  have hf : Integrable (fun ξ : ℝ ↦ Real.exp (-b * ξ ^ 2) * ‖charFun μ ξ‖ ^ 2) := by
    apply ((integrable_exp_neg_mul_sq hb).mul_const (μ.real univ ^ 2)).mono' (by fun_prop)
    exact Eventually.of_forall fun ξ ↦ by
      have hs := (sq_le_sq₀ (norm_nonneg _) ENNReal.toReal_nonneg).mpr
        (norm_charFun_le (μ := μ) ξ)
      simpa only [measureReal_def, Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ Real.exp (-b * ξ ^ 2) * ‖charFun μ ξ‖ ^ 2)] using
          mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
  have hk : Integrable (fun p : ℝ × ℝ ↦
      Real.exp (-((p.1 - p.2) ^ 2 / (4 * b)))) (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Eventually.of_forall fun p ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity))
  have hf' := ofReal_integral_eq_lintegral_ofReal hf
    (Eventually.of_forall fun ξ ↦ mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have hk' := ofReal_integral_eq_lintegral_ofReal hk
    (Eventually.of_forall fun p ↦ Real.exp_nonneg _)
  simp_rw [sq_abs, ← ENNReal.ofReal_mul (Real.exp_nonneg _), Real.dist_eq, sq_abs]
  rw [← hf', ← hk', ← ENNReal.ofReal_mul (by positivity),
    integral_gaussian_charFun_norm_sq_real μ hb]

/-- The weighted characteristic-function energy corresponding to one-dimensional Riesz energy. -/
def rieszFourierEnergy1D (μ : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (t - 1) * ENNReal.ofReal (‖charFun μ ξ‖ ^ 2)

/-- Exact Fourier/Riesz identity, with both positive Gamma factors displayed. -/
theorem rieszFourierEnergy1D_mul_gamma
    (μ : Measure ℝ) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    ENNReal.ofReal (Real.Gamma ((1 - t) / 2)) * rieszFourierEnergy1D μ t =
      ENNReal.ofReal (Real.pi ^ (1 / 2 : ℝ) * Real.Gamma (t / 2) * (4 : ℝ) ^ (t / 2)) *
        rieszEnergy1D μ t := by
  have h := riesz_fourier_identity_of_gaussian volume (μ.prod μ)
    (ρ := fun ξ : ℝ ↦ |ξ|) (σ := fun p : ℝ × ℝ ↦ dist p.1 p.2)
    (by fun_prop) (by fun_prop) abs_nonneg (fun _ ↦ dist_nonneg)
    (f := fun ξ ↦ ENNReal.ofReal (‖charFun μ ξ‖ ^ 2)) (by fun_prop)
    ht ht₁ (fun b hb ↦ lintegral_gaussian_charFun_norm_sq_real μ hb)
  rw [lintegral_prod _ (by fun_prop)] at h
  exact h

/-- The one-dimensional Fourier/Riesz identity, valid also when the energies are infinite. -/
theorem rieszFourierEnergy1D_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    rieszFourierEnergy1D μ t =
      ENNReal.ofReal (rieszFourierConstant 1 t) * rieszEnergy1D μ t := by
  have hg := Real.Gamma_pos_of_pos (show 0 < (1 - t) / 2 by linarith)
  have h := (ENNReal.eq_div_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hg))
    ENNReal.ofReal_ne_top).mpr (rieszFourierEnergy1D_mul_gamma μ ht ht₁)
  rw [rieszFourierConstant, ENNReal.ofReal_div_of_pos hg]
  exact h.trans (by simp only [div_eq_mul_inv]; ring)

/-- Finite spatial energy gives a genuinely finite weighted Fourier square integral. -/
theorem rieszFourierEnergy1D_lt_top
    (μ : Measure ℝ) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (ht₁ : t < 1)
    (hE : rieszEnergy1D μ t < ∞) : rieszFourierEnergy1D μ t < ∞ := by
  rw [rieszFourierEnergy1D_eq μ ht ht₁]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE

end FalconerPacking
