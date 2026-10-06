/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RetainedChainDistance
public import FalconerPacking.RetainedEnergyConstants

/-!
# Absorbing the fixed Fourier constants

Only four nonnegative scalar terms remain: the chain main term, spatial localization,
initial reconstruction and omitted spectral energy. This module absorbs every fixed
Schwartz and polar constant uniformly over the entire annular family.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- The fixed analytic factors have one finite bound independent of the block and shell. -/
theorem exists_retained_energy_constant_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (B C₄ : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T k : ℕ) (X Y Z W : ℝ≥0∞),
      ENNReal.ofReal ((sourceCutoffRadius χ hχ + B) * (2 * Real.pi) ^ 2) *
        (2 * (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
            (81 * ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
              SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) * X + Y) *
            (∫⁻ x, ‖initialCircleMultiplierRadius B x‖ₑ ^ 2) *
            ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 (𝓕 (dyadicAnnularKernel T k))) ^ 2) *
            (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal C₄ + 2 * Z + W) ≤
        ENNReal.ofReal C * (X + Y + Z + W) := by
  let l := ENNReal.ofReal ((sourceCutoffRadius χ hχ + B) * (2 * Real.pi) ^ 2)
  let u := ∫⁻ x, ‖unitReproducingKernel x‖ₑ
  let v := 81 * ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
    SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel)
  let i := ∫⁻ x, ‖initialCircleMultiplierRadius B x‖ₑ ^ 2
  let c := 2 * u * i * 4 * (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal C₄
  let S := l * c * v + l * c + l * 2 + l
  have hu : u ≠ ⊤ := by
    rw [show u = _ from lintegral_enorm_unitReproducingKernel_eq_ofReal]
    exact ENNReal.ofReal_ne_top
  have hi : i ≠ ⊤ := (lintegral_sq_initialCircleMultiplierRadius_lt_top B).ne
  have hp : (ENNReal.ofReal (2 * Real.pi))⁻¹ ≠ ⊤ := by
    simp only [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (by positivity)
  have hS : S ≠ ⊤ := by
    dsimp [S, c, v, l]
    finiteness
  let C := S.toReal + 1
  have hSC : S ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hS]
    apply ENNReal.ofReal_le_ofReal
    dsimp [C]
    linarith
  have hXC : l * c * v ≤ ENNReal.ofReal C :=
    (show l * c * v ≤ S by exact le_add_right (le_add_right le_self_add)).trans hSC
  have hYC : l * c ≤ ENNReal.ofReal C :=
    (show l * c ≤ S by exact le_add_right (le_add_right le_add_self)).trans hSC
  have hZC : l * 2 ≤ ENNReal.ofReal C :=
    (show l * 2 ≤ S by exact le_add_right le_add_self).trans hSC
  have hWC : l ≤ ENNReal.ofReal C :=
    (show l ≤ S by exact le_add_self).trans hSC
  refine ⟨C, by dsimp [C]; exact le_add_of_nonneg_left ENNReal.toReal_nonneg, ?_⟩
  intro T k X Y Z W
  calc
    _ ≤ l * (c * (v * X + Y) + 2 * Z + W) := by
      dsimp only [l, c, u, v, i]
      grw [ofReal_sq_seminorm_fourier_dyadicAnnularKernel_le T k]
      exact le_of_eq (by ring)
    _ = (l * c * v) * X + (l * c) * Y + (l * 2) * Z + l * W := by ring
    _ ≤ ENNReal.ofReal C * X + ENNReal.ofReal C * Y +
        ENNReal.ofReal C * Z + ENNReal.ofReal C * W := by gcongr
    _ = _ := by ring

/-- The full actual retained density is bounded by four scalar expressions and one
fixed finite coefficient. The pin measure is the normalized regular component. -/
theorem exists_retainedChain_four_term_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) {J : ℕ} (hJ : 0 < J) {B : ℝ} (hB : 0 ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (q m pwr K : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {d C₀ : ℝ} (hd : 0 ≤ d) (hd₂ : d ≤ 2) (hfr : IsFrostman μ d C₀) :
    ∃ C₁ C₂ C₃ C₅ C : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < C₅ ∧ 1 ≤ C ∧ ∃ k₀ : ℕ,
      ∀ (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M),
        (∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure σ],
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
        (∫⁻ p, ENNReal.ofReal (‖complexDistanceDensity (f p.1) p.1 p.2‖ ^ 2)
          ∂σ.prod volume) ≤ ENNReal.ofReal C *
            (ENNReal.ofReal ((4 * R) ^ 2) * ENNReal.ofReal (L ^ 2 * a 0) ^ 2 * chain *
                ENNReal.ofReal (1 / R₀) * ENNReal.ofReal ((2 * R) ^ (2 - d)) +
              ENNReal.ofReal (((4 * R) ^ 2 * C₂ /
                (1 + 4 * R * (L ^ 2 * a 0 / 2 - a 0)) ^ m) *
                (1 / R₀) * (2 * R) ^ (2 - d)) +
              ENNReal.ofReal ((C₁ / ((2 : ℝ) ^ k) ^ q) ^ 2 * (2 * R) ^ 2) +
              ENNReal.ofReal (C₅ / ((2 : ℝ) ^ k) ^ q)) := by
  obtain ⟨C₁, C₂, C₃, C₄, C₅, hC₁, hC₂, hC₃, hC₄, hC₅, k₀, hc⟩ :=
    exists_retainedChain_distance_energy_bound χ hχ hχone hJ hB hδ q m pwr K μ hd hd₂ hfr
  obtain ⟨C, hC, hfixed⟩ := exists_retained_energy_constant_bound χ hχ B C₄
  refine ⟨C₁, C₂, C₃, C₅, C, hC₁, hC₂, hC₃, hC₅, hC, k₀, ?_⟩
  intro M hμ hnear σ _ hball k hk
  dsimp only
  intro n e hn he he₀ t het L hL H I hcurv hscale₀ hscale₁ hframe
  apply (hc M hμ hnear σ hball k hk n e hn he he₀ t het L hL H I
    hcurv hscale₀ hscale₁ hframe).trans
  dsimp only
  simp only [measure_univ, mul_one]
  let R₀ : ℝ := 2 ^ (4 * J * k)
  let R : ℝ := 2 ^ (4 * J + 2) * R₀
  let a : ℝ := ((2 : ℝ) ^ n 0)⁻¹
  have hR : 0 < R := by dsimp [R, R₀]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hden : 0 ≤ 1 + 4 * R * (L ^ 2 * a / 2 - a) := by
    have hLa : 0 ≤ L ^ 2 * a / 2 - a := by nlinarith [sq_nonneg (L - 1)]
    positivity
  have hrad : 0 ≤ (2 * R) ^ (2 - d) := Real.rpow_nonneg (by positivity) _
  have hloc : 0 ≤ (4 * R) ^ 2 * C₂ / (1 + 4 * R * (L ^ 2 * a / 2 - a)) ^ m :=
    div_nonneg (mul_nonneg (sq_nonneg _) hC₂.le) (pow_nonneg hden _)
  have hF := hfixed (4 * J) k
    (ENNReal.ofReal ((4 * R) ^ 2) * ENNReal.ofReal (L ^ 2 * a) ^ 2 *
      ((∏ j ∈ Finset.range K, ENNReal.ofReal C₃ * ENNReal.ofReal (L ^ (8 * j + 14)) * H j) *
          ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) +
        ∑ j ∈ Finset.range K,
          (∏ i ∈ Finset.range j, ENNReal.ofReal C₃ * ENNReal.ofReal (L ^ (8 * i + 14)) * H i) *
          (ENNReal.ofReal C₃ * ENNReal.ofReal
            (((((2 : ℝ) ^ n j)⁻¹) ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
            ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2))) *
      ENNReal.ofReal (1 / R₀) * ENNReal.ofReal ((2 * R) ^ (2 - d)))
    (ENNReal.ofReal ((4 * R) ^ 2 * C₂ /
      (1 + 4 * R * (L ^ 2 * a / 2 - a)) ^ m) *
      ENNReal.ofReal (1 / R₀) * ENNReal.ofReal ((2 * R) ^ (2 - d)))
    (ENNReal.ofReal (C₁ / ((2 : ℝ) ^ k) ^ q) ^ 2 * ENNReal.ofReal ((2 * R) ^ 2))
    (ENNReal.ofReal (C₅ / ((2 : ℝ) ^ k) ^ q))
  rw [ENNReal.ofReal_mul hC₄.le]
  rw [ENNReal.ofReal_mul (mul_nonneg hloc (by positivity)),
    ENNReal.ofReal_mul hloc,
    ENNReal.ofReal_mul (sq_nonneg (C₁ / ((2 : ℝ) ^ k) ^ q)),
    ENNReal.ofReal_pow (div_nonneg hC₁.le (by positivity))]
  convert hF using 1 <;> first | rfl | (simp only [R, R₀, a]; ring)

end FalconerPacking
