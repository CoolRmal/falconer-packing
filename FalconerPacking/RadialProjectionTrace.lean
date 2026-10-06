/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RieszFourier1D
public import FalconerPacking.RadialProjectionTraceWeight

/-!
# Fourier trace estimates for finite measures

Weighted Cauchy--Schwarz is applied to the genuine Fourier pairing with a Schwartz
test function. Extended nonnegative energies keep every bound valid before finiteness
has been established.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- Cauchy--Schwarz with complementary homogeneous frequency weights. -/
theorem enorm_integral_mul_sq_le_weighted
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g) (t : ℝ) :
    ‖∫ ξ : ℝ, f ξ * g ξ‖ₑ ^ 2 ≤
      (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (t - 1) * ‖f ξ‖ₑ ^ 2) *
      (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - t) * ‖g ξ‖ₑ ^ 2) := by
  let u : ℝ → ℝ≥0∞ := fun ξ ↦ ENNReal.ofReal |ξ| ^ ((t - 1) / 2) * ‖f ξ‖ₑ
  let v : ℝ → ℝ≥0∞ := fun ξ ↦ ENNReal.ofReal |ξ| ^ ((1 - t) / 2) * ‖g ξ‖ₑ
  have hu : Measurable u := by fun_prop
  have hv : Measurable v := by fun_prop
  have heq : (∫⁻ ξ : ℝ, ‖f ξ * g ξ‖ₑ) = ∫⁻ ξ : ℝ, u ξ * v ξ := by
    apply lintegral_congr_ae
    have hzero : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by simp [ae_iff]
    filter_upwards [hzero] with ξ hξ
    have hpos : ENNReal.ofReal |ξ| ≠ 0 := (ENNReal.ofReal_pos.mpr (abs_pos.mpr hξ)).ne'
    dsimp [u, v]
    rw [enorm_mul]
    symm
    calc
      _ = (ENNReal.ofReal |ξ| ^ ((t - 1) / 2) *
          ENNReal.ofReal |ξ| ^ ((1 - t) / 2)) * (‖f ξ‖ₑ * ‖g ξ‖ₑ) := by ac_rfl
      _ = ‖f ξ‖ₑ * ‖g ξ‖ₑ := by
        rw [← ENNReal.rpow_add _ _ hpos ENNReal.ofReal_ne_top,
          show (t - 1) / 2 + (1 - t) / 2 = 0 by ring, ENNReal.rpow_zero, one_mul]
  have hu₂ : (∫⁻ ξ : ℝ, u ξ ^ (2 : ℝ)) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (t - 1) * ‖f ξ‖ₑ ^ 2 := by
    apply lintegral_congr
    intro ξ
    dsimp only [u]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.rpow_mul, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_two]
  have hv₂ : (∫⁻ ξ : ℝ, v ξ ^ (2 : ℝ)) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - t) * ‖g ξ‖ₑ ^ 2 := by
    apply lintegral_congr
    intro ξ
    dsimp only [v]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.rpow_mul, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_two]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (2 : ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    hu.aemeasurable hv.aemeasurable
  rw [hu₂, hv₂] at hh
  have h := (enorm_integral_le_lintegral_enorm (fun ξ ↦ f ξ * g ξ)).trans (heq.trans_le hh)
  apply (pow_le_pow_left' h 2).trans_eq
  rw [mul_pow]
  simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- A Schwartz test against a finite measure is controlled by complementary Fourier energies. -/
theorem enorm_integral_schwartz_sq_le_weighted_fourier
    (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : SchwartzMap ℝ ℂ) (t : ℝ) :
    ‖∫ x, φ x ∂μ‖ₑ ^ 2 ≤
      (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (t - 1) * ‖measureFourier μ ξ‖ₑ ^ 2) *
      (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - t) * ‖(𝓕⁻ φ) ξ‖ₑ ^ 2) := by
  rw [integral_schwartz_eq_measureFourier]
  exact enorm_integral_mul_sq_le_weighted (continuous_measureFourier μ).measurable
    (𝓕⁻ φ).continuous.measurable t

/-- Spatial dilation produces the matching dilation of a characteristic function. -/
theorem charFun_map_mul_real (μ : Measure ℝ) [IsFiniteMeasure μ] (a ξ : ℝ) :
    charFun (μ.map (fun x ↦ a * x)) ξ = charFun μ (a * ξ) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), charFun_apply_real]
  congr 1
  funext x
  congr 1
  push_cast
  ring

/-- Riesz energy scales directly on the spatial side, including infinite energies. -/
theorem rieszEnergy1D_map_mul (μ : Measure ℝ) [SFinite μ] (a t : ℝ) :
    rieszEnergy1D (μ.map (fun x ↦ a * x)) t =
      ENNReal.ofReal |a| ^ (-t) * rieszEnergy1D μ t := by
  unfold rieszEnergy1D
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  have hmap (x : ℝ) : (∫⁻ y, ENNReal.ofReal (dist x y) ^ (-t)
      ∂μ.map (fun z ↦ a * z)) = ∫⁻ y, ENNReal.ofReal (dist x (a * y)) ^ (-t) ∂μ :=
    lintegral_map (by fun_prop) (by fun_prop)
  simp_rw [hmap]
  simp only [Real.dist_eq, ← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg a),
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  have hconst (x : ℝ) := lintegral_const_mul (ENNReal.ofReal |a| ^ (-t))
    (show Measurable (fun y : ℝ ↦ ENNReal.ofReal |x - y| ^ (-t)) from by fun_prop)
    (μ := μ)
  simp_rw [hconst]
  rw [lintegral_const_mul _ (by fun_prop)]

/-- The Fourier normalization factor can be obtained by dilating the spatial measure. -/
theorem weighted_measureFourier_eq_rieszEnergy
    (μ : Measure ℝ) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (t - 1) * ‖measureFourier μ ξ‖ₑ ^ 2) =
      ENNReal.ofReal (rieszFourierConstant 1 t) *
        ENNReal.ofReal (2 * Real.pi) ^ (-t) * rieszEnergy1D μ t := by
  let μ' := μ.map (fun x ↦ (-2 * Real.pi) * x)
  have heq (ξ : ℝ) : measureFourier μ ξ = charFun μ' ξ := by
    rw [charFun_map_mul_real, measureFourier_eq_charFun]
  simp_rw [heq]
  have h := rieszFourierEnergy1D_eq μ' ht ht₁
  rw [rieszEnergy1D_map_mul] at h
  simpa only [rieszFourierEnergy1D, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0),
    abs_of_pos Real.pi_pos, neg_neg, mul_assoc] using h

/-- The actual Fourier/Riesz trace estimate for a finite measure and a Schwartz function. -/
theorem enorm_integral_schwartz_sq_le_rieszEnergy
    (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : SchwartzMap ℝ ℂ)
    {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    ‖∫ x, φ x ∂μ‖ₑ ^ 2 ≤
      (ENNReal.ofReal (rieszFourierConstant 1 t) *
        ENNReal.ofReal (2 * Real.pi) ^ (-t) * rieszEnergy1D μ t) *
      (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - t) * ‖(𝓕⁻ φ) ξ‖ₑ ^ 2) := by
  simpa only [weighted_measureFourier_eq_rieszEnergy μ ht ht₁] using
    enorm_integral_schwartz_sq_le_weighted_fourier μ φ t

end FalconerPacking
