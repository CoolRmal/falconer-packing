/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialProjectionTrace

/-!
# Positive level-set estimates from Riesz trace bounds

Restriction and Hölder give an energy bound with the correct power of the retained mass.
This applies the Fourier trace estimate to actual level-set restrictions of the pin measure.
-/

noncomputable section

open MeasureTheory Set SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- Restricting a measure gains the mass factor dictated by product Hölder. -/
theorem rieszEnergy1D_restrict_le
    (μ : Measure ℝ) [SFinite μ] (A : Set ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q) (a : ℝ) :
    rieszEnergy1D (μ.restrict A) a ≤
      rieszEnergy1D μ (p * a) ^ (1 / p) * μ A ^ (2 / q) := by
  let κ := μ.restrict A
  let k : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (dist z.1 z.2) ^ (-a)
  have hk : Measurable k := by fun_prop
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (κ.prod κ) hpq
    hk.aemeasurable (show AEMeasurable (fun _ : ℝ × ℝ ↦ (1 : ℝ≥0∞)) _ from
      measurable_const.aemeasurable)
  have hkint : (∫⁻ z, k z ∂κ.prod κ) = rieszEnergy1D κ a := by
    rw [lintegral_prod _ hk.aemeasurable]
    rfl
  have hkp : (∫⁻ z, k z ^ p ∂κ.prod κ) = rieszEnergy1D κ (p * a) := by
    rw [lintegral_prod _ (hk.pow_const p).aemeasurable]
    simp only [k, rieszEnergy1D, ← ENNReal.rpow_mul, neg_mul, mul_comm a p]
  have hmass : ((κ.prod κ) univ) ^ (1 / q) = μ A ^ (2 / q) := by
    rw [← univ_prod_univ, Measure.prod_prod]
    simp only [κ, Measure.restrict_apply_univ, ← pow_two,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    norm_num
    ring
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one] at hh
  rw [hkint, hkp, hmass] at hh
  apply hh.trans
  apply mul_le_mul_left
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hpq.nonneg)
  unfold rieszEnergy1D κ
  apply lintegral_mono' μ.restrict_le_self
  intro x
  exact lintegral_mono' μ.restrict_le_self (fun _ ↦ le_rfl)

/-- Positivity on a level set controls its mass by the genuine restricted Fourier pairing. -/
theorem mul_measure_schwartz_level_le_enorm_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : SchwartzMap ℝ ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal T * μ {x | T ≤ (φ x).re} ≤
      ‖∫ x in {x | T ≤ (φ x).re}, φ x ∂μ‖ₑ := by
  let A := {x | T ≤ (φ x).re}
  have hA : MeasurableSet A := measurableSet_le measurable_const (by fun_prop)
  have hint : Integrable (fun x ↦ φ x) (μ.restrict A) :=
    φ.toBoundedContinuousFunction.integrable (μ.restrict A)
  have hnonneg : 0 ≤ᵐ[μ.restrict A] fun x ↦ (φ x).re := by
    filter_upwards [ae_restrict_mem hA] with x hx
    exact hT.trans hx
  calc
    ENNReal.ofReal T * μ A = ∫⁻ _ : ℝ, ENNReal.ofReal T ∂μ.restrict A := by simp
    _ ≤ ∫⁻ x, ENNReal.ofReal (φ x).re ∂μ.restrict A := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      exact ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal (∫ x, (φ x).re ∂μ.restrict A) :=
      (ofReal_integral_eq_lintegral_ofReal hint.re hnonneg).symm
    _ = ENNReal.ofReal ((∫ x, φ x ∂μ.restrict A).re) := by
      simpa only [RCLike.re_eq_complex_re] using congrArg ENNReal.ofReal (integral_re hint)
    _ ≤ ‖∫ x, φ x ∂μ.restrict A‖ₑ := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)

/-- The mass-sensitive trace estimate on each positive level set. -/
theorem schwartz_level_trace_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : SchwartzMap ℝ ℂ)
    {p q a T : ℝ} (hpq : p.HolderConjugate q)
    (ha : 0 < a) (ha₁ : a < 1) (hT : 0 ≤ T) :
    (ENNReal.ofReal T * μ {x | T ≤ (φ x).re}) ^ 2 ≤
      (ENNReal.ofReal (rieszFourierConstant 1 a) *
        ENNReal.ofReal (2 * Real.pi) ^ (-a)) *
      (rieszEnergy1D μ (p * a) ^ (1 / p) * μ {x | T ≤ (φ x).re} ^ (2 / q)) *
      (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - a) * ‖(𝓕⁻ φ) ξ‖ₑ ^ 2) := by
  apply (pow_le_pow_left' (mul_measure_schwartz_level_le_enorm_integral μ φ hT) 2).trans
  apply (enorm_integral_schwartz_sq_le_rieszEnergy
    (μ.restrict {x | T ≤ (φ x).re}) φ ha ha₁).trans
  exact mul_le_mul_left (mul_le_mul_right (rieszEnergy1D_restrict_le μ _ hpq a) _) _

/-- Canceling the finite level-set mass yields the weak trace exponent. -/
theorem ennreal_tail_bound_of_mass_trace
    {p q : ℝ} (hpq : p.HolderConjugate q) {T z K : ℝ≥0∞}
    (hz : z ≠ ∞) (h : (T * z) ^ 2 ≤ K * z ^ (2 / q)) :
    T ^ p * z ≤ K ^ (p / 2) := by
  by_cases hz₀ : z = 0
  · simp [hz₀]
  have hsum : 2 / p + 2 / q = 2 := by
    have hh := hpq.inv_add_inv_eq_one
    simp only [div_eq_mul_inv]
    linarith
  have hsplit : z ^ (2 : ℕ) = z ^ (2 / p) * z ^ (2 / q) := by
    rw [← ENNReal.rpow_add _ _ hz₀ hz, hsum, ENNReal.rpow_two]
  have hcancel : T ^ (2 : ℕ) * z ^ (2 / p) ≤ K := by
    apply (ENNReal.mul_le_mul_iff_left
      (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hz₀) hz).ne'
      (ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hpq.symm.nonneg) hz)).mp
    simpa only [mul_pow, hsplit, mul_assoc] using h
  have hpow := ENNReal.rpow_le_rpow hcancel (div_nonneg hpq.nonneg (by norm_num : (0 : ℝ) ≤ 2))
  have heq : (T ^ (2 : ℕ) * z ^ (2 / p)) ^ (p / 2) = T ^ p * z := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg hpq.nonneg (by norm_num : (0 : ℝ) ≤ 2)),
      ← ENNReal.rpow_natCast T 2, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (p / 2) = p by ring,
      show (2 / p) * (p / 2) = 1 by field_simp [hpq.pos.ne'], ENNReal.rpow_one]
  rwa [heq] at hpow

/-- A genuine weak-`L^p` trace bound for a Schwartz function against a finite measure. -/
theorem schwartz_level_weak_trace_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : SchwartzMap ℝ ℂ)
    {p q a T : ℝ} (hpq : p.HolderConjugate q)
    (ha : 0 < a) (ha₁ : a < 1) (hT : 0 ≤ T) :
    ENNReal.ofReal T ^ p * μ {x | T ≤ (φ x).re} ≤
      (ENNReal.ofReal (rieszFourierConstant 1 a) *
        ENNReal.ofReal (2 * Real.pi) ^ (-a)) ^ (p / 2) *
      rieszEnergy1D μ (p * a) ^ (1 / 2 : ℝ) *
      (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - a) * ‖(𝓕⁻ φ) ξ‖ₑ ^ 2) ^ (p / 2) := by
  have h := schwartz_level_trace_bound μ φ hpq ha ha₁ hT
  have h' := ennreal_tail_bound_of_mass_trace hpq
    (measure_ne_top μ {x | T ≤ (φ x).re})
    (show (ENNReal.ofReal T * μ {x | T ≤ (φ x).re}) ^ 2 ≤
      ((ENNReal.ofReal (rieszFourierConstant 1 a) *
        ENNReal.ofReal (2 * Real.pi) ^ (-a)) * rieszEnergy1D μ (p * a) ^ (1 / p) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - a) * ‖(𝓕⁻ φ) ξ‖ₑ ^ 2)) *
        μ {x | T ≤ (φ x).re} ^ (2 / q) from by convert h using 1; ac_rfl)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg hpq.nonneg (by norm_num : (0 : ℝ) ≤ 2)),
    ← ENNReal.rpow_mul, show (1 / p) * (p / 2) = (1 / 2 : ℝ) by
      field_simp [hpq.pos.ne']] using h'

end FalconerPacking
