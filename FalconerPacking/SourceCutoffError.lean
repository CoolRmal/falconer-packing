/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.LocalizedPacketMass
public import FalconerPacking.PhysicalCapRadialTails

/-!
# Removing the fixed source cutoff with an actual error bound

A cutoff equal to one in a neighborhood of the source changes a convolved measure only
through the kernel tail outside that neighborhood. The same first-norm bound controls
the literal Fourier transform of the error at every frequency.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- The actual error from a fixed cutoff is bounded by the radial kernel tail. -/
theorem lintegral_enorm_source_cutoff_error_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hχ : Continuous χ) (hχone : ∀ x, |χ x| ≤ 1)
    (δ : ℝ) (hnear : ∀ᵐ y ∂μ, ∀ x, ‖x - y‖ < δ → χ x = 1) :
    (∫⁻ x, ‖(1 - χ x) • schwartzMeasureDensity μ K x‖ₑ) ≤
      2 * (∫⁻ z in {z | δ ≤ ‖z‖}, ‖K z‖ₑ) * μ univ := by
  let V := {z : EuclideanSpace ℝ (Fin 2) | δ ≤ ‖z‖}
  let A := ∫⁻ z in V, ‖K z‖ₑ
  have hV : MeasurableSet V := isClosed_le continuous_const continuous_norm |>.measurableSet
  have he (x) : ‖1 - χ x‖ₑ ≤ 2 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat]
    apply ENNReal.ofReal_le_ofReal
    exact (abs_sub _ _).trans (by rw [abs_one]; linarith [hχone x])
  have hpoint (y : EuclideanSpace ℝ (Fin 2)) (hy : ∀ x, ‖x - y‖ < δ → χ x = 1) :
      (∫⁻ x, ‖1 - χ x‖ₑ * ‖K (x - y)‖ₑ) ≤ 2 * A := by
    calc
      _ ≤ ∫⁻ x, 2 * V.indicator (fun z ↦ ‖K z‖ₑ) (x - y) := by
        apply lintegral_mono
        intro x
        dsimp only
        by_cases hx : χ x = 1
        · simp only [hx, sub_self, enorm_zero, zero_mul, zero_le]
        · have hfar : x - y ∈ V := le_of_not_gt (fun h ↦ hx (hy x h))
          rw [indicator_of_mem hfar]
          exact mul_le_mul' (he x) le_rfl
      _ = 2 * A := by
        rw [lintegral_const_mul' 2 _ (by norm_num), lintegral_sub_right_eq_self,
          lintegral_indicator hV]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖1 - χ x‖ₑ * ‖K (x - y)‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      have hm : Measurable (fun y ↦ ‖K (x - y)‖ₑ) :=
        (K.continuous.measurable.comp (measurable_const.sub measurable_id)).enorm
      rw [enorm_smul, lintegral_const_mul _ hm]
      exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
    _ = ∫⁻ y, ∫⁻ x, ‖1 - χ x‖ₑ * ‖K (x - y)‖ₑ ∂volume ∂μ :=
      lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ _y, 2 * A ∂μ := lintegral_mono_ae (hnear.mono hpoint)
    _ = _ := by rw [lintegral_const]

/-- The literal Fourier integral of the actual cutoff error obeys the same tail bound. -/
theorem enorm_fourier_source_cutoff_error_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hχ : Continuous χ) (hχone : ∀ x, |χ x| ≤ 1)
    (δ : ℝ) (hnear : ∀ᵐ y ∂μ, ∀ x, ‖x - y‖ < δ → χ x = 1)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖(𝓕 (fun x ↦ (1 - χ x) • schwartzMeasureDensity μ K x)) ξ‖ₑ ≤
      2 * (∫⁻ z in {z | δ ≤ ‖z‖}, ‖K z‖ₑ) * μ univ := by
  apply le_trans ?_ (lintegral_enorm_source_cutoff_error_le μ K χ hχ hχone δ hnear)
  rw [Real.fourier_eq]
  apply (enorm_integral_le_lintegral_enorm _).trans_eq
  congr 1
  funext x
  rw [← ofReal_norm, ← ofReal_norm, Circle.norm_smul]

end FalconerPacking
