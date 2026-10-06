/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourceCutoffError

/-!
# Uniform removal of the fixed source cutoff for actual caps

All kernel tails are discharged using the constructed dyadic caps. The resulting bound
is simultaneous in cap index, annular scale, and spectral frequency.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- Removing the source cutoff incurs an arbitrarily rapid first-norm and Fourier error. -/
theorem exists_uniform_dyadic_source_cutoff_error {ι : Type*} (T : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (n N j : ι → ℕ) (hN : ∀ i, 0 < N i)
    (hwidth : ∀ i, Real.sqrt ((2 : ℝ) ^ (T * n i)) ≤ N i)
    (hsmall : ∀ i, 4 * Real.pi ≤ N i)
    (hupper : ∀ i, (N i : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n i)))
    (m : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hχ : Continuous χ) (hχone : ∀ x, |χ x| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hnear : ∀ᵐ y ∂μ, ∀ x, ‖x - y‖ < δ → χ x = 1) :
    ∃ C > 0, ∀ i,
      let Kᵢ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
        𝓕⁻ (dyadicAngularCap T (n i) (N i) (hN i) (j i))
      let error := fun x ↦ (1 - χ x) • schwartzMeasureDensity μ Kᵢ x
      let B := ENNReal.ofReal (C / (Real.sqrt ((2 : ℝ) ^ (T * n i)) * δ) ^ m) * μ univ
      (∫⁻ x, ‖error x‖ₑ) ≤ B ∧ ∀ ξ, ‖(𝓕 error) ξ‖ₑ ≤ B := by
  obtain ⟨C, hC, htail⟩ :=
    dyadicCapKernel_uniform_radial_tail T hK n N j hN hwidth hsmall hupper m
  refine ⟨2 * C, by positivity, fun i ↦ ?_⟩
  dsimp only
  let Kᵢ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
    𝓕⁻ (dyadicAngularCap T (n i) (N i) (hN i) (j i))
  have hb : 2 * (∫⁻ z in {z | δ ≤ ‖z‖}, ‖Kᵢ z‖ₑ) * μ univ ≤
      ENNReal.ofReal (2 * C / (Real.sqrt ((2 : ℝ) ^ (T * n i)) * δ) ^ m) * μ univ := by
    apply (mul_le_mul' (mul_le_mul' le_rfl (htail i δ hδ)) le_rfl).trans_eq
    congr 1
    rw [show 2 * C / (Real.sqrt ((2 : ℝ) ^ (T * n i)) * δ) ^ m =
      2 * (C / (Real.sqrt ((2 : ℝ) ^ (T * n i)) * δ) ^ m) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  exact ⟨(lintegral_enorm_source_cutoff_error_le μ Kᵢ χ hχ hχone δ hnear).trans hb,
    fun ξ ↦ (enorm_fourier_source_cutoff_error_le μ Kᵢ χ hχ hχone δ hnear ξ).trans hb⟩

end FalconerPacking
