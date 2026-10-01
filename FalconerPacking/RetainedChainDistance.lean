/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RetainedCircleChain
import FalconerPacking.RetainedDistanceEnergy

/-!
# The full retained distance density from the actual Fourier chain

This composes initial reconstruction, the marked Fourier chain, polar source integration,
the actual omitted-frequency estimate and Liu's identity. All remaining hypotheses concern
the finite chain geometry. The source and its Fourier transform are common to all pin cells.
-/

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- The actual retained good density obeys the complete chain estimate over all distances.
The displayed errors include both initial reconstruction and the noncompact Fourier tails. -/
theorem exists_retainedChain_distance_energy_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) {J : ℕ} (hJ : 0 < J) {B : ℝ} (hB : 0 ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (q m pwr K : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {d C₀ : ℝ} (hd : 0 ≤ d) (hd₂ : d ≤ 2) (hfr : IsFrostman μ d C₀) :
    ∃ C₁ C₂ C₃ C₄ C₅ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < C₄ ∧ 0 < C₅ ∧ ∃ k₀ : ℕ,
      ∀ (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M),
        (∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ],
        (∀ᵐ y ∂σ, ‖y‖ ≤ B) → ∀ k ≥ k₀,
        let s := 6 + 2 * J * k
        let w := (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * J)
        let ψ := 𝓕 (dyadicAnnularKernel (4 * J) k)
        let hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) k
        let hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * J) k
        let R₀ := (2 : ℝ) ^ (4 * J * k)
        let R := (2 : ℝ) ^ (4 * J + 2) * R₀
        ∀ (n e : ℕ → ℕ), Antitone n → Monotone e → e 0 = 0 →
        ∀ t : ℕ, e K ≤ t → ∀ L : ℝ, 346 ≤ L →
        ∀ (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)),
        let a := fun j ↦ ((2 : ℝ) ^ n j)⁻¹
        (∀ j < K, a (j + 1) ≤ R * (a j) ^ 2) →
        (∀ j < K, R * a j ≤ (2 : ℝ) ^ e (j + 1)) →
        (∀ j < K, (2 : ℝ) ^ e (j + 1) ≤ 2 * (R * a j)) →
        (∀ j < K, s < e (j + 1) → ((2 : ℝ) ^ s)⁻¹ ≤ a j / a (j + 1)) →
        let f := retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w
        let A := fun j ↦ ENNReal.ofReal C₃ * ENNReal.ofReal (L ^ (8 * j + 14)) * H j
        let err := fun j ↦ ENNReal.ofReal C₃ *
          ENNReal.ofReal (((a j) ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
          ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2)
        let chain := (∏ j ∈ Finset.range K, A j) *
          ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) +
          ∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) * err j
        let D := ENNReal.ofReal ((4 * R) ^ 2) * 81 *
          ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
            SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) *
          ENNReal.ofReal (L ^ 2 * a 0) ^ 2
        let T := ENNReal.ofReal ((4 * R) ^ 2 * C₂ /
          (1 + 4 * R * (L ^ 2 * a 0 / 2 - a 0)) ^ m)
        (∫⁻ p, ENNReal.ofReal (‖complexDistanceDensity (f p.1) p.1 p.2‖ ^ 2)
          ∂σ.prod volume) ≤
          ENNReal.ofReal ((sourceCutoffRadius χ hχ + B) * (2 * Real.pi) ^ 2) *
            (2 * (∫⁻ x, ‖unitReproducingKernel x‖ₑ) * (D * chain + T) * σ univ *
                (∫⁻ x, ‖initialCircleMultiplierRadius B x‖ₑ ^ 2) *
                ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
                ENNReal.ofReal (1 / R₀) * (ENNReal.ofReal (2 * Real.pi))⁻¹ *
                ENNReal.ofReal (C₄ * (2 * R) ^ (2 - d)) +
              2 * ENNReal.ofReal (C₁ / ((2 : ℝ) ^ k) ^ q) ^ 2 * σ univ *
                ENNReal.ofReal ((2 * R) ^ 2) +
              σ univ * ENNReal.ofReal (C₅ / ((2 : ℝ) ^ k) ^ q)) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, k₀, hc⟩ :=
    exists_retainedCircle_chain_bound χ hχ hχone hJ B hδ q m pwr K
      ((2 : ℝ) ^ (4 * J + 2)) (by positivity)
  obtain ⟨C₄, C₅, hC₄, hC₅, hdensity⟩ :=
    exists_retainedPinDistance_energy_bound χ hχ hJ q μ hd hd₂ hfr
  refine ⟨C₁, C₂, C₃, C₄, C₅, hC₁, hC₂, hC₃, hC₄, hC₅, k₀, ?_⟩
  intro M hμ hnear σ _ hball k hk
  dsimp only
  intro n e hn he he₀ t het L hL H I hcurv hscale₀ hscale₁ hframe
  apply hdensity M hμ k σ σ n e t K L H I B hB hball
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hR : 1 ≤ (2 : ℝ) ^ (4 * J + 2) * 2 ^ (4 * J * k) := by
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := 4 * J + 2),
      one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := 4 * J * k)]
  have hratio : (2 : ℝ) ^ (4 * J + 2) * 2 ^ (4 * J * k) ≤
      (2 : ℝ) ^ (4 * J + 2) * r :=
    mul_le_mul_of_nonneg_left hr.1.le (by positivity)
  have hc' := hc μ M hμ hnear σ hball k hk n e hn he he₀ t het L hL H I
    ((2 : ℝ) ^ (4 * J + 2) * 2 ^ (4 * J * k)) r hR hr.1.le hratio hr.2.le
    hcurv hscale₀ hscale₁ hframe
  rw [lintegral_retainedPinSource_spectral]
  dsimp only at hc'
  apply hc'.trans
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one]
  exact le_of_eq (by ring)

end FalconerPacking
