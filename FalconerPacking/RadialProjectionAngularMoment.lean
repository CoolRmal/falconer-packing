/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionWeakMoment

/-!
# Averaging positive trace level sets

The probability bound interpolates the directional weak trace estimate to a joint exponent
strictly greater than one. Only the first angular moments of the two Fourier energies enter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Averaged directional weak traces require only first moments of both energies. -/
theorem lintegral_trace_tail_interpolate {α : Type*} [MeasurableSpace α]
    (σ : Measure α) {m E H : α → ℝ≥0∞}
    (hm : Measurable m) (hE : Measurable E) (hH : Measurable H)
    {p : ℝ} (hp : 1 < p) {T C : ℝ≥0∞}
    (hm₁ : ∀ x, m x ≤ 1)
    (htrace : ∀ x, T ^ p * m x ≤ C ^ (p / 2) * E x ^ (1 / 2 : ℝ) * H x ^ (p / 2)) :
    T ^ (2 * p / (p + 1)) * (∫⁻ x, m x ∂σ) ≤
      C ^ (p / (p + 1)) * (∫⁻ x, E x ∂σ) ^ (1 / (p + 1)) *
        (∫⁻ x, H x ∂σ) ^ (p / (p + 1)) := by
  have hp₀ : 0 < p := by linarith
  have hsum₀ : 0 < p + 1 := by linarith
  have hr₀ : 0 ≤ 2 / (p + 1) := div_nonneg (by norm_num) hsum₀.le
  have hr₁ : 2 / (p + 1) ≤ 1 := (div_le_one hsum₀).mpr (by linarith)
  have hpoint (x : α) : T ^ (2 * p / (p + 1)) * m x ≤
      C ^ (p / (p + 1)) * (E x ^ (1 / (p + 1)) * H x ^ (p / (p + 1))) := by
    have hh := ennreal_tail_bound_interpolate (hm₁ x) hr₀ hr₁ (htrace x)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ hr₀, ← ENNReal.rpow_mul,
      show p * (2 / (p + 1)) = 2 * p / (p + 1) by ring,
      show (p / 2) * (2 / (p + 1)) = p / (p + 1) by ring,
      show (1 / 2 : ℝ) * (2 / (p + 1)) = 1 / (p + 1) by ring,
      mul_assoc] using hh
  have hconj : (p + 1).HolderConjugate ((p + 1) / p) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    field_simp
    ring
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq σ hconj
    (hE.pow_const (1 / (p + 1))).aemeasurable
    (hH.pow_const (p / (p + 1))).aemeasurable
  have hnormE : (∫⁻ x, (E x ^ (1 / (p + 1))) ^ (p + 1) ∂σ) = ∫⁻ x, E x ∂σ := by
    simp only [← ENNReal.rpow_mul, one_div_mul_cancel hsum₀.ne', ENNReal.rpow_one]
  have hnormH : (∫⁻ x, (H x ^ (p / (p + 1))) ^ ((p + 1) / p) ∂σ) =
      ∫⁻ x, H x ∂σ := by
    simp only [← ENNReal.rpow_mul, show (p / (p + 1)) * ((p + 1) / p) = 1 by
      field_simp, ENNReal.rpow_one]
  rw [hnormE, hnormH, show 1 / ((p + 1) / p) = p / (p + 1) by field_simp] at hholder
  calc
    _ = ∫⁻ x, T ^ (2 * p / (p + 1)) * m x ∂σ := (lintegral_const_mul _ hm).symm
    _ ≤ ∫⁻ x, C ^ (p / (p + 1)) *
        (E x ^ (1 / (p + 1)) * H x ^ (p / (p + 1))) ∂σ := lintegral_mono hpoint
    _ = C ^ (p / (p + 1)) * ∫⁻ x,
        E x ^ (1 / (p + 1)) * H x ^ (p / (p + 1)) ∂σ :=
      lintegral_const_mul _ ((hE.pow_const _).mul (hH.pow_const _))
    _ ≤ _ := by simpa only [Pi.mul_apply, mul_assoc] using
        mul_le_mul_right hholder (C ^ (p / (p + 1)))

end FalconerPacking
