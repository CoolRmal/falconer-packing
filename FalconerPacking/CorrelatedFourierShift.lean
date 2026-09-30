/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CorrelatedAngles
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fourier translation multipliers with correlated shifts

The translation multiplier is controlled before integration over the common pin parameter.
The shift therefore needs no independence from the direction or the Fourier amplitude.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- The complex translation multiplier has the quadratic bound and the trivial bound. -/
theorem enorm_translation_multiplier_sq_le (t : ℝ) :
    ‖Complex.exp (Complex.I * t) - 1‖ₑ ^ 2 ≤
      min 4 (ENNReal.ofReal (t ^ 2)) := by
  apply le_min
  · have h : ‖Complex.exp (Complex.I * t) - 1‖ ≤ 2 := by
      simpa only [norm_one, Complex.norm_exp, Complex.mul_re, Complex.I_re,
        Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
        sub_zero, Real.exp_zero, one_add_one_eq_two] using
          norm_sub_le (Complex.exp (Complex.I * t)) 1
    have hs : ‖Complex.exp (Complex.I * t) - 1‖ ^ 2 ≤ (4 : ℝ) := by
      nlinarith [norm_nonneg (Complex.exp (Complex.I * t) - 1)]
    simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hs
  · have h := pow_le_pow_left' (Real.enorm_exp_I_mul_ofReal_sub_one_le (x := t)) 2
    simpa only [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs] using h

/-- A bounded parameter-dependent translation changes an amplitude by a uniform multiplier. -/
theorem enorm_shifted_amplitude_sq_le {τ v δ : ℝ} (hv : |v| ≤ δ) (z : ℂ) :
    ‖Complex.exp (Complex.I * (τ * v)) * z - z‖ₑ ^ 2 ≤
      min 4 (ENNReal.ofReal (τ ^ 2 * δ ^ 2)) * ‖z‖ₑ ^ 2 := by
  rw [← sub_one_mul, enorm_mul, mul_pow]
  apply mul_le_mul' _ le_rfl
  rw [← Complex.ofReal_mul]
  refine (enorm_translation_multiplier_sq_le (τ * v)).trans (min_le_min le_rfl ?_)
  apply ENNReal.ofReal_le_ofReal
  have hδ : 0 ≤ δ := (abs_nonneg v).trans hv
  have hv₂ : v ^ 2 ≤ δ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg v) hδ).mpr hv
  nlinarith [mul_le_mul_of_nonneg_left hv₂ (sq_nonneg τ)]

/-- Averaging the translation bound requires only the angular marginal, even for a shift
depending arbitrarily on the same parameter. -/
theorem lintegral_correlated_translation_le
    {α : Type*} [MeasurableSpace α] (κ : Measure α) {θ v : α → ℝ}
    (hθ : Measurable θ) {A : ℝ≥0∞} (hdom : κ.map θ ≤ A • (volume : Measure ℝ))
    {F : ℝ → ℂ} (hF : Continuous F) {a b τ δ : ℝ}
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc a b) (hshift : ∀ᵐ z ∂κ, |v z| ≤ δ) :
    ∫⁻ z, ‖Complex.exp (Complex.I * (τ * v z)) * F (θ z) - F (θ z)‖ₑ ^ 2 ∂κ ≤
      (min 4 (ENNReal.ofReal (τ ^ 2 * δ ^ 2))) *
        (A * ∫⁻ t in Icc a b, ‖F t‖ₑ ^ 2) := by
  let G := (Icc a b).indicator (fun t ↦ ‖F t‖ₑ ^ 2)
  have hG : Measurable G := (hF.enorm.measurable.pow_const 2).indicator measurableSet_Icc
  have hc : min 4 (ENNReal.ofReal (τ ^ 2 * δ ^ 2)) ≠ ∞ :=
    ne_top_of_le_ne_top (by norm_num) (min_le_left _ _)
  calc
    _ ≤ ∫⁻ z, min 4 (ENNReal.ofReal (τ ^ 2 * δ ^ 2)) * G (θ z) ∂κ := by
      apply lintegral_mono_ae
      filter_upwards [hrange, hshift] with z hz hv
      simpa only [G, indicator_of_mem hz] using enorm_shifted_amplitude_sq_le hv (F (θ z))
    _ = min 4 (ENNReal.ofReal (τ ^ 2 * δ ^ 2)) * ∫⁻ z, G (θ z) ∂κ :=
      lintegral_const_mul' _ _ hc
    _ ≤ min 4 (ENNReal.ofReal (τ ^ 2 * δ ^ 2)) * (A * ∫⁻ t, G t) :=
      mul_le_mul' le_rfl (lintegral_comp_le_of_map_le_smul κ hθ hdom hG)
    _ = _ := by rw [lintegral_indicator measurableSet_Icc]

/-- Fubini applies the angular derivative estimate to an entire frequency band. -/
theorem lintegral_correlated_angular_band_le
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    {θ φ : α → ℝ} (hθ : Measurable θ) (hφ : Measurable φ) {A : ℝ≥0∞}
    (hdom : κ.map θ ≤ A • (volume : Measure ℝ))
    {F F' : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ τ t, HasDerivAt (F τ) (F' τ t) t)
    (S : Set ℝ) {a b h : ℝ} (hh : 0 ≤ h)
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc a b ∧ φ z ∈ Icc a b)
    (hclose : ∀ᵐ z ∂κ, |φ z - θ z| ≤ h) :
    ∫⁻ z, ∫⁻ τ in S, ‖F τ (φ z) - F τ (θ z)‖ₑ ^ 2 ∂volume ∂κ ≤
      (A * ENNReal.ofReal (2 * h ^ 2)) *
        ∫⁻ τ in S, ∫⁻ t in Icc a b, ‖F' τ t‖ₑ ^ 2 := by
  have hm : Measurable (fun p : α × ℝ ↦ ‖F p.2 (φ p.1) - F p.2 (θ p.1)‖ₑ ^ 2) := by
    exact ((hF.measurable.comp (measurable_snd.prodMk (hφ.comp measurable_fst))).sub
      (hF.measurable.comp (measurable_snd.prodMk (hθ.comp measurable_fst)))).enorm.pow_const 2
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ τ in S, (A * ENNReal.ofReal (2 * h ^ 2)) *
        ∫⁻ t in Icc a b, ‖F' τ t‖ₑ ^ 2 := by
      apply lintegral_mono
      intro τ
      exact lintegral_correlated_angular_difference_le κ hθ hdom (hderiv τ)
        (hF'.comp (continuous_const.prodMk continuous_id)) hh hrange hclose
    _ = _ := lintegral_const_mul _ (hF'.measurable.enorm.pow_const 2).lintegral_prod_right

/-- The translation multiplier can be bounded uniformly on a prescribed frequency band. -/
theorem lintegral_correlated_translation_band_le
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    {θ v : α → ℝ} (hθ : Measurable θ) (hv : Measurable v) {A : ℝ≥0∞}
    (hdom : κ.map θ ≤ A • (volume : Measure ℝ))
    {F : ℝ → ℝ → ℂ} (hF : Continuous (Function.uncurry F))
    {S : Set ℝ} (hS : MeasurableSet S) {a b R δ : ℝ}
    (hR : 0 ≤ R) (hband : ∀ τ ∈ S, |τ| ≤ R)
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc a b) (hshift : ∀ᵐ z ∂κ, |v z| ≤ δ) :
    ∫⁻ z, ∫⁻ τ in S,
      ‖Complex.exp (Complex.I * (τ * v z)) * F τ (θ z) - F τ (θ z)‖ₑ ^ 2 ∂volume ∂κ ≤
      (min 4 (ENNReal.ofReal (R ^ 2 * δ ^ 2))) *
        (A * ∫⁻ τ in S, ∫⁻ t in Icc a b, ‖F τ t‖ₑ ^ 2) := by
  have hm : Measurable (fun p : α × ℝ ↦
      ‖Complex.exp (Complex.I * (p.2 * v p.1)) * F p.2 (θ p.1) -
        F p.2 (θ p.1)‖ₑ ^ 2) := by
    have hc : Measurable (fun p : α × ℝ ↦ F p.2 (θ p.1)) :=
      hF.measurable.comp (measurable_snd.prodMk (hθ.comp measurable_fst))
    have he : Measurable (fun p : α × ℝ ↦ Complex.exp (Complex.I * (p.2 * v p.1))) :=
      Complex.continuous_exp.measurable.comp
        (measurable_const.mul (measurable_snd.complex_ofReal.mul
          (hv.comp measurable_fst).complex_ofReal))
    exact ((he.mul hc).sub hc).enorm.pow_const 2
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ τ in S, (min 4 (ENNReal.ofReal (R ^ 2 * δ ^ 2))) *
        (A * ∫⁻ t in Icc a b, ‖F τ t‖ₑ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with τ hτ
      refine (lintegral_correlated_translation_le κ hθ hdom
        (hF.comp (continuous_const.prodMk continuous_id)) hrange hshift).trans ?_
      apply mul_le_mul' _ le_rfl
      apply min_le_min le_rfl
      apply ENNReal.ofReal_le_ofReal
      have hτsq : τ ^ 2 ≤ R ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg τ) hR).mpr (hband τ hτ)
      exact mul_le_mul_of_nonneg_right hτsq (sq_nonneg δ)
    _ = _ := by
      have he : Measurable (fun τ ↦ ∫⁻ t in Icc a b, ‖F τ t‖ₑ ^ 2) :=
        (hF.measurable.enorm.pow_const 2).lintegral_prod_right
      rw [lintegral_const_mul' _ _ (ne_top_of_le_ne_top (by norm_num) (min_le_left _ _)),
        lintegral_const_mul _ he]

end FalconerPacking
